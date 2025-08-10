// ---- Helpers ----
const toBytes = (hex) => {
    const h = hex.trim().toLowerCase();
    if (!/^[0-9a-f]*$/.test(h) || h.length % 2) throw new Error("Invalid hex");
    return new Uint8Array(h.match(/.{2}/g).map((b) => parseInt(b, 16)));
};
const hex = (buf) => Array.from(buf, (b) => b.toString(16).padStart(2, "0")).join("");
const leHex = (buf) => hex(buf.slice().reverse());
const readU32 = (v, o) => (v[o] | (v[o + 1] << 8) | (v[o + 2] << 16) | (v[o + 3] << 24)) >>> 0;
const readU64LE = (v, o) => {
    // returns BigInt
    let lo = BigInt(readU32(v, o));
    let hi = BigInt(readU32(v, o + 4));
    return lo | (hi << 32n);
};
function readVarInt(v, o) {
    const first = v[o];
    if (first < 0xfd) return { n: first, size: 1 };
    if (first === 0xfd) return { n: v[o + 1] | (v[o + 2] << 8), size: 3 };
    if (first === 0xfe) return { n: readU32(v, o + 1), size: 5 };
    // 0xff
    const n = readU64LE(v, o + 1);
    return { n, size: 9 };
}
function slice(v, o, len) { return v.slice(o, o + len); }

// ---- Base58 & Bech32 for address formatting ----
const ALPHABET = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz";
const ALPHABET_MAP = Object.fromEntries([...ALPHABET].map((c, i) => [c, i]));
function base58encode(bytes) {
    // bitcoin-style base58 encode
    let digits = [0];
    for (const b of bytes) {
        let carry = b;
        for (let j = 0; j < digits.length; j++) {
            const x = digits[j] * 256 + carry;
            digits[j] = x % 58;
            carry = Math.floor(x / 58);
        }
        while (carry) { digits.push(carry % 58); carry = Math.floor(carry / 58); }
    }
    // leading zeros
    let zeros = 0; for (const b of bytes) { if (b === 0) zeros++; else break; }
    return "1".repeat(zeros) + digits.reverse().map(d => ALPHABET[d]).join("");
}
async function sha256(buf) { const h = await crypto.subtle.digest("SHA-256", buf); return new Uint8Array(h); }
async function base58check(version, payload) {
    const data = new Uint8Array(1 + payload.length + 4);
    data[0] = version;
    data.set(payload, 1);
    const h1 = await sha256(data.slice(0, 1 + payload.length));
    const h2 = await sha256(h1);
    data.set(h2.slice(0, 4), 1 + payload.length);
    return base58encode(data);
}

// bech32
const CHARSET = "qpzry9x8gf2tvdw0s3jn54khce6mua7l";
const CHARKEY = Object.fromEntries([...CHARSET].map((c, i) => [c, i]));
function bech32Polymod(values) {
    const GENERATORS = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3];
    let chk = 1;
    for (const v of values) {
        const top = chk >>> 25;
        chk = ((chk & 0x1ffffff) << 5) ^ v;
        for (let i = 0; i < 5; i++) if ((top >>> i) & 1) chk ^= GENERATORS[i];
    }
    return chk >>> 0;
}
function bech32HrpExpand(hrp) { const r = []; for (const c of hrp) r.push(c.charCodeAt(0) >> 5); r.push(0); for (const c of hrp) r.push(c.charCodeAt(0) & 31); return r; }
function bech32CreateChecksum(hrp, data, spec) {
    const values = [...bech32HrpExpand(hrp), ...data, 0, 0, 0, 0, 0, 0];
    const pm = bech32Polymod(values) ^ (spec === "bech32m" ? 0x2bc830a3 : 1);
    const ret = []; for (let p = 0; p < 6; p++) ret.push((pm >>> (5 * (5 - p))) & 31);
    return ret;
}
function convertBits(data, from, to, pad) {
    let acc = 0, bits = 0; const ret = []; const maxv = (1 << to) - 1;
    for (const value of data) {
        if (value < 0 || (value >> from) !== 0) return null;
        acc = (acc << from) | value; bits += from;
        while (bits >= to) { bits -= to; ret.push((acc >> bits) & maxv); }
    }
    if (pad) { if (bits > 0) ret.push((acc << (to - bits)) & maxv); }
    else if (bits >= from || ((acc << (to - bits)) & maxv)) return null;
    return ret;
}
function bech32Encode(hrp, witver, program) {
    const data = [witver, ...convertBits(program, 8, 5, true)];
    const spec = witver === 0 ? "bech32" : "bech32m";
    const checksum = bech32CreateChecksum(hrp, data, spec);
    return hrp + "1" + data.concat(checksum).map(v => CHARSET[v]).join("");
}

// ---- Script recognition ----
function classifyScriptPubKey(spk, network) {
    const h = spk.toLowerCase();
    // P2PKH: 76 a9 14 <20> 88 ac
    if (h.startsWith("76a914") && h.length === (25 * 2) && h.endsWith("88ac")) {
        const hash160 = h.slice(6, 46);
        const payload = new Uint8Array(hash160.match(/.{2}/g).map(x => parseInt(x, 16)));
        const version = network === "mainnet" ? 0x00 : 0x6f;
        return { type: "P2PKH", addressPromise: base58check(version, payload) };
    }
    // P2SH: a9 14 <20> 87
    if (h.startsWith("a914") && h.length === (23 * 2) && h.endsWith("87")) {
        const hash160 = h.slice(4, 44);
        const payload = new Uint8Array(hash160.match(/.{2}/g).map(x => parseInt(x, 16)));
        const version = network === "mainnet" ? 0x05 : 0xc4;
        return { type: "P2SH", addressPromise: base58check(version, payload) };
    }
    // P2WPKH: 00 14 <20>
    if (h.startsWith("0014") && h.length === (22 * 2)) {
        const prog = new Uint8Array(h.slice(4).match(/.{2}/g).map(x => parseInt(x, 16)));
        const hrp = network === "mainnet" ? "bc" : network === "regtest" ? "bcrt" : "tb";
        return { type: "P2WPKH", addressPromise: Promise.resolve(bech32Encode(hrp, 0, prog)) };
    }
    // P2WSH: 00 20 <32>
    if (h.startsWith("0020") && h.length === (34 * 2)) {
        const prog = new Uint8Array(h.slice(4).match(/.{2}/g).map(x => parseInt(x, 16)));
        const hrp = network === "mainnet" ? "bc" : network === "regtest" ? "bcrt" : "tb";
        return { type: "P2WSH", addressPromise: Promise.resolve(bech32Encode(hrp, 0, prog)) };
    }
    // P2TR: 51 20 <32>
    if (h.startsWith("5120") && h.length === (34 * 2)) {
        const prog = new Uint8Array(h.slice(4).match(/.{2}/g).map(x => parseInt(x, 16)));
        const hrp = network === "mainnet" ? "bc" : network === "regtest" ? "bcrt" : "tb";
        return { type: "P2TR", addressPromise: Promise.resolve(bech32Encode(hrp, 1, prog)) };
    }
    return { type: "nonstandard", addressPromise: Promise.resolve(null) };
}

// ---- TX Decoder ----
function decodeTxHex(hexStr) {
    const v = toBytes(hexStr);
    let o = 0;
    const version = readU32(v, o); o += 4;

    // segwit check: marker=0x00, flag=0x01
    let segwit = false;
    if (v[o] === 0x00 && v[o + 1] === 0x01) { segwit = true; o += 2; }

    // vin
    let vi = readVarInt(v, o); const vinCount = Number(vi.n); o += vi.size;
    const vin = [];
    for (let i = 0; i < vinCount; i++) {
        const prev = slice(v, o, 32); o += 32;
        const txid = leHex(prev);
        const vout = readU32(v, o); o += 4;
        let vs = readVarInt(v, o); o += vs.size;
        const scriptSig = slice(v, o, Number(vs.n)); o += Number(vs.n);
        const sequence = readU32(v, o); o += 4;
        vin.push({ txid, vout, scriptSigHex: hex(scriptSig), sequence });
    }

    // vout
    vi = readVarInt(v, o); const voutCount = Number(vi.n); o += vi.size;
    const voutArr = [];
    let totalOut = 0n;
    for (let i = 0; i < voutCount; i++) {
        const value = readU64LE(v, o); o += 8;
        let vsz = readVarInt(v, o); o += vsz.size;
        const spk = slice(v, o, Number(vsz.n)); o += Number(vsz.n);
        totalOut += value;
        voutArr.push({ value, scriptPubKeyHex: hex(spk) });
    }

    // witnesses
    const witness = [];
    if (segwit) {
        for (let i = 0; i < vinCount; i++) {
            let nStack = readVarInt(v, o); o += nStack.size;
            const stack = [];
            for (let s = 0; s < Number(nStack.n); s++) {
                const l = readVarInt(v, o); o += l.size;
                const item = slice(v, o, Number(l.n)); o += Number(l.n);
                stack.push(hex(item));
            }
            witness.push(stack);
        }
    }

    const locktime = readU32(v, o); o += 4;

    return { version, segwit, vinCount, voutCount, vin, vout: voutArr, witness, locktime, totalOut };
}

// ---- UI ----
function satsToBTC(sats) { return Number((BigInt(sats) / 1000n) / 1000000n) + (Number(BigInt(sats) % 100000000n) / 1e8); }
function fmtSats(s) { return `${s} sats (${(Number(s) / 1e8).toFixed(8)} BTC)`; }

function el(html) { const d = document.createElement("div"); d.innerHTML = html.trim(); return d.firstChild; }

async function render(tx, network) {
    // summary
    document.getElementById("version").textContent = tx.version;
    document.getElementById("segwit").textContent = tx.segwit ? "Yes" : "No";
    document.getElementById("vinCount").textContent = tx.vinCount;
    document.getElementById("voutCount").textContent = tx.voutCount;
    document.getElementById("locktime").textContent = tx.locktime;
    document.getElementById("totalOut").textContent = fmtSats(tx.totalOut.toString());

    // inputs
    const inputs = document.getElementById("inputs");
    inputs.innerHTML = "";
    tx.vin.forEach((i, idx) => {
        const html = `<details class="rounded-xl border border-zinc-200 dark:border-zinc-700 p-3">
      <summary class="font-medium">#${idx} — ${i.txid}:${i.vout}</summary>
      <div class="mt-3 text-xs grid gap-2">
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">TXID</div><div class="font-mono break-all">${i.txid}</div></div>
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">VOUT</div><div class="">${i.vout}</div></div>
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">scriptSig</div><div class="font-mono break-all">${i.scriptSigHex || "(empty)"}</div></div>
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">sequence</div><div class="font-mono">${"0x" + i.sequence.toString(16).padStart(8, "0")}</div></div>
      </div>
    </details>`;
        inputs.appendChild(el(html));
    });

    // outputs
    const outputs = document.getElementById("outputs");
    outputs.innerHTML = "";
    for (let idx = 0; idx < tx.vout.length; idx++) {
        const o = tx.vout[idx];
        const cls = classifyScriptPubKey(o.scriptPubKeyHex, network);
        const address = await cls.addressPromise;
        const html = `<details class="rounded-xl border border-zinc-200 dark:border-zinc-700 p-3">
      <summary class="font-medium">#${idx} — ${fmtSats(o.value.toString())}${address ? " → " + address : ""}</summary>
      <div class="mt-3 text-xs grid gap-2">
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">Value</div><div class="font-mono">${fmtSats(o.value.toString())}</div></div>
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">Type</div><div>${cls.type}</div></div>
        <div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">scriptPubKey</div><div class="font-mono break-all">${o.scriptPubKeyHex}</div></div>
        ${address ? `<div class="grid sm:grid-cols-[140px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">Address</div><div class="font-mono break-all">${address}</div></div>` : ""}
      </div>
    </details>`;
        outputs.appendChild(el(html));
    }

    // witness
    const wwrap = document.getElementById("witnessWrap");
    const w = document.getElementById("witness");
    if (tx.segwit) {
        wwrap.classList.remove("hidden"); w.innerHTML = "";
        tx.witness.forEach((stack, i) => {
            const items = stack.map((s, idx) => `<div class="grid sm:grid-cols-[100px_1fr] gap-3"><div class="text-zinc-500 dark:text-zinc-400">item ${idx}</div><div class="font-mono break-all">${s || "(empty)"}</div></div>`).join("");
            w.appendChild(el(`<details class="rounded-xl border border-zinc-200 dark:border-zinc-700 p-3"><summary class="font-medium">Input #${i}</summary><div class="mt-3 text-xs grid gap-2">${items || "(no items)"}</div></details>`));
        });
    } else {
        wwrap.classList.add("hidden");
    }
}

function decodeAndRender() {
    const resultWrap = document.getElementById("resultWrap");
    const errorWrap = document.getElementById("errorWrap");
    const err = document.getElementById("err");
    try {
        const t = document.getElementById("tx").value.trim();
        const network = document.getElementById("network").value;
        const tx = decodeTxHex(t);
        render(tx, network);
        resultWrap.classList.remove("hidden");
        errorWrap.classList.add("hidden");
    } catch (e) {
        resultWrap.classList.add("hidden");
        errorWrap.classList.remove("hidden");
        err.textContent = e.message || String(e);
    }
}

document.addEventListener("DOMContentLoaded", () => {
    document.getElementById("decodeBtn").addEventListener("click", decodeAndRender);
    document.getElementById("tx").addEventListener("keydown", (e) => { if (e.key === "Enter" && (e.ctrlKey || e.metaKey)) decodeAndRender(); });
    // demo tx (p2wpkh spend w/ change) — truncated if needed by user
    document.getElementById("tx").value = "";
});