'use strict';
// ============================================================================
// Official BLAKE3 conformance test (all three modes, full extended output).
//
// Runs against the canonical test_vectors.json from the BLAKE3 repo
// (35 input lengths, 0..102400 bytes, input = repeating 0,1,2,...,250).
//
// For every vector x mode it checks BOTH:
//   - the 32-byte API           (hash / keyedHash / deriveKey)
//   - the full extended output  (hashXOF / keyedHashXOF / deriveKeyXOF),
//     matching all 131 bytes the vector specifies.
//
// Modes: hash (plain), keyed_hash (32-byte key), derive_key (context string).
// ============================================================================
const fs = require('fs');
const path = require('path');
const {
  hash, hashXOF,
  keyedHash, keyedHashXOF,
  deriveKey, deriveKeyXOF,
  toHex,
} = require('./blake3-ultra.js');

const tv = JSON.parse(fs.readFileSync(path.join(__dirname, 'test_vectors.json'), 'utf8'));
const keyBytes = new TextEncoder().encode(tv.key);          // 32-byte key
const context = tv.context_string;

function genInput(n) {
  const a = new Uint8Array(n);
  for (let i = 0; i < n; i++) a[i] = i % 251;
  return a;
}

const modes = {
  hash:       { field: 'hash',       h32: (i) => hash(i),                 xof: (i, n) => hashXOF(i, n) },
  keyed_hash: { field: 'keyed_hash', h32: (i) => keyedHash(keyBytes, i),  xof: (i, n) => keyedHashXOF(keyBytes, i, n) },
  derive_key: { field: 'derive_key', h32: (i) => deriveKey(context, i),   xof: (i, n) => deriveKeyXOF(context, i, n) },
};

let totalFail = 0;
let xofBytes = 0;
for (const [name, m] of Object.entries(modes)) {
  let pass = 0;
  let fail = 0;
  for (const c of tv.cases) {
    const inp = genInput(c.input_len);
    const full = c[m.field];                 // full extended output, hex
    const outLen = full.length / 2;          // 131 bytes for these vectors
    xofBytes = outLen;

    const got32 = toHex(m.h32(inp));
    const gotXof = toHex(m.xof(inp, outLen));

    if (got32 === full.slice(0, 64) && gotXof === full) {
      pass++;
    } else {
      fail++;
      console.log(`FAIL [${name}] len=${c.input_len}`);
      if (got32 !== full.slice(0, 64)) console.log(`  32B  exp ${full.slice(0, 64)}\n       got ${got32}`);
      if (gotXof !== full) console.log(`  XOF  exp ${full}\n       got ${gotXof}`);
    }
  }
  totalFail += fail;
  console.log(`${name.padEnd(11)}: ${pass}/${tv.cases.length} PASS, ${fail} FAIL  (32-byte + ${xofBytes}-byte XOF)`);
}

console.log(totalFail === 0
  ? `\nFully conformant: ${tv.cases.length} vectors x 3 modes x (32-byte + ${xofBytes}-byte XOF).`
  : `\n${totalFail} total failures.`);
if (totalFail > 0) process.exit(1);
