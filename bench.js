'use strict';
// ============================================================================
// Head-to-head throughput benchmark.
//
// Compares this repo's two builds against:
//   - blake3-ultra (pure JS) and blake3-simd (WASM SIMD)  -> this repo
//   - Node's native (OpenSSL C) SHA-256 / SHA-512         -> "optimized native" anchor
//   - @noble/hashes BLAKE3 (pure JS)                      -> direct pure-JS peer (if installed)
//
// Note: SHA-256/512 are different algorithms; they are anchors for "how fast is
// the machine's optimized native hashing", not apples-to-apples with BLAKE3.
// The apples-to-apples comparison is the @noble/hashes BLAKE3 row.
//
// Run:  node bench.js   (after `npm install` to include the @noble peer)
// ============================================================================
const crypto = require('crypto');
const { hash } = require('./blake3-ultra.js');
const { hash: hashSimd } = require('./blake3-simd.js');

let nobleBlake3 = null;
try {
  nobleBlake3 = require('@noble/hashes/blake3').blake3;
} catch (e) {
  // optional peer not installed
}

function makeData(size) {
  const a = new Uint8Array(size);
  for (let i = 0; i < size; i++) a[i] = i & 0xff;
  return a;
}

const competitors = [
  { name: 'blake3-ultra (this, pure JS)', fn: (d) => hash(d) },
  { name: 'blake3-simd (this, WASM SIMD)', fn: (d) => hashSimd(d) },
  { name: 'node sha256 (native C)',       fn: (d) => crypto.createHash('sha256').update(d).digest() },
  { name: 'node sha512 (native C)',       fn: (d) => crypto.createHash('sha512').update(d).digest() },
];
if (nobleBlake3) {
  competitors.push({ name: '@noble/hashes blake3 (pure JS)', fn: (d) => nobleBlake3(d) });
}

console.log('BLAKE3-ULTRA head-to-head throughput');
console.log('='.repeat(70));
if (!nobleBlake3) {
  console.log('NOTE: @noble/hashes not installed - run `npm install` to add the pure-JS peer.\n');
}

// JIT warmup: each implementation gets a heavy, equal warmup so the comparison
// reflects steady-state optimized code, not cold interpretation.
const warm = makeData(64 * 1024);
process.stdout.write('Warming up JIT...');
for (const c of competitors) {
  for (let i = 0; i < 4000; i++) c.fn(warm);
}
console.log(' done\n');

const sizes = [
  [1024,             '1 KiB',  20000],
  [64 * 1024,        '64 KiB',  4000],
  [1024 * 1024,      '1 MiB',    300],
  [10 * 1024 * 1024, '10 MiB',    20],
];

for (const [size, label, iters] of sizes) {
  const data = makeData(size);
  console.log(`${label} x ${iters}:`);
  for (const c of competitors) {
    for (let i = 0; i < 5; i++) c.fn(data); // per-size warmup
    const t0 = process.hrtime.bigint();
    for (let i = 0; i < iters; i++) c.fn(data);
    const t1 = process.hrtime.bigint();
    const sec = Number(t1 - t0) / 1e9;
    const mib = (size * iters) / sec / (1024 * 1024);
    console.log(`  ${c.name.padEnd(34)} ${mib.toFixed(1).padStart(9)} MiB/s  (${(mib / 1024).toFixed(3)} GiB/s)`);
  }
  console.log();
}
