'use strict';

// ============================================================================
// BLAKE3 SIMD - Step 9 of the Fleek "Blake3: A JavaScript Optimization Case
// Study" (the blog the BLAKE3-in-JavaScript bounty was based on).
//
// A 4-wide (i32x4) compress4x is generated as WebAssembly SIMD *at load time* -
// no .wasm file is shipped; the module is assembled from JavaScript and compiled
// synchronously, so hash() stays synchronous and this remains a single JS file.
//
// The fully-unrolled scalar compress (shared with blake3-ultra.js) handles small
// inputs, parent merges, and the tail; compress4x hashes 4 chunks in parallel
// for the bulk.
//
// Credits:
//   - WASM compress4x bytecode generator: the Fleek "Blake3: A JavaScript
//     Optimization Case Study" blog (step 9), which documents the byte sequences.
//     https://blog.fleek.network/post/fleek-network-blake3-case-study/
//   - The parallel-chunk ORCHESTRATION (the blog calls this "future work" and
//     omits it) is adapted from the bounty entry Bk3JS by Rilsosing Koireng
//     (github.com/chimmykk/Bk3JS): the wasm memory offsets, the 4-chunk -> 3
//     parent-compress subtree merge, the (length-1)/4096 SIMD boundary, and the
//     ((length-offset-1)|1023)-1023 tail formula follow that implementation.
//
// Scope: plain hash mode, 32-byte output only (no keyed/derive/XOF - those live
// in blake3-ultra.js). Little-endian fast path with a scalar fallback.
// ============================================================================

const BLOCK_LEN = 64;
const CHUNK_LEN = 1024;
const CHUNK_START = 1;
const CHUNK_END = 2;
const PARENT = 4;
const ROOT = 8;

const IV = new Uint32Array([
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]);

const IS_LITTLE_ENDIAN = new Uint8Array(new Uint32Array([1]).buffer)[0] === 1;

let cvStack = null;
const blockWords = new Uint32Array(16);
const outWords = new Uint32Array(16);

function ensureCvStack(maxDepth) {
  const depth = Math.max(maxDepth | 0, 10) | 0;
  const length = (depth * 8) | 0;
  if (cvStack === null || cvStack.length < length) {
    cvStack = new Uint32Array(length);
  }
  return cvStack;
}

function readWordsLE(bytes, offset, words, count) {
  for (let i = 0; i < count; i = i + 1 | 0, offset = offset + 4 | 0) {
    words[i] = (bytes[offset] |
                (bytes[offset + 1 | 0] << 8) |
                (bytes[offset + 2 | 0] << 16) |
                (bytes[offset + 3 | 0] << 24)) | 0;
  }
  for (let i = count; i < 16; i = i + 1 | 0) {
    words[i] = 0;
  }
}

function readPartialBlock(bytes, offset, length, words) {
  words.fill(0);
  let i = 0;
  for (; i + 3 < length; i = i + 4 | 0) {
    const idx = i >> 2;
    words[idx] = (bytes[offset + i] |
                  (bytes[offset + i + 1 | 0] << 8) |
                  (bytes[offset + i + 2 | 0] << 16) |
                  (bytes[offset + i + 3 | 0] << 24)) | 0;
  }
  if (i < length) {
    const idx = i >> 2;
    let word = 0;
    for (let shift = 0; i < length; i = i + 1 | 0, shift = shift + 8 | 0) {
      word |= bytes[offset + i | 0] << shift;
    }
    words[idx] = word | 0;
  }
}

function compress(cv, cvOff, msg, msgOff, out, outOff, counter, blockLen, flags, truncate) {
  let s0 = cv[cvOff] | 0;
  let s1 = cv[cvOff + 1 | 0] | 0;
  let s2 = cv[cvOff + 2 | 0] | 0;
  let s3 = cv[cvOff + 3 | 0] | 0;
  let s4 = cv[cvOff + 4 | 0] | 0;
  let s5 = cv[cvOff + 5 | 0] | 0;
  let s6 = cv[cvOff + 6 | 0] | 0;
  let s7 = cv[cvOff + 7 | 0] | 0;
  let s8 = 0x6a09e667 | 0;
  let s9 = 0xbb67ae85 | 0;
  let s10 = 0x3c6ef372 | 0;
  let s11 = 0xa54ff53a | 0;
  let s12 = counter | 0;
  let s13 = 0;
  let s14 = blockLen | 0;
  let s15 = flags | 0;

  const m0 = msg[msgOff] | 0;
  const m1 = msg[msgOff + 1 | 0] | 0;
  const m2 = msg[msgOff + 2 | 0] | 0;
  const m3 = msg[msgOff + 3 | 0] | 0;
  const m4 = msg[msgOff + 4 | 0] | 0;
  const m5 = msg[msgOff + 5 | 0] | 0;
  const m6 = msg[msgOff + 6 | 0] | 0;
  const m7 = msg[msgOff + 7 | 0] | 0;
  const m8 = msg[msgOff + 8 | 0] | 0;
  const m9 = msg[msgOff + 9 | 0] | 0;
  const m10 = msg[msgOff + 10 | 0] | 0;
  const m11 = msg[msgOff + 11 | 0] | 0;
  const m12 = msg[msgOff + 12 | 0] | 0;
  const m13 = msg[msgOff + 13 | 0] | 0;
  const m14 = msg[msgOff + 14 | 0] | 0;
  const m15 = msg[msgOff + 15 | 0] | 0;

  // ===== ROUND 0 ===== Schedule: [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
  // Column mixing
  s0 = (s0 + s4 | 0) + m0 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m1 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m2 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m3 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m4 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m5 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m6 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m7 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  // Diagonal mixing
  s0 = (s0 + s5 | 0) + m8 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m9 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m10 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m11 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m12 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m13 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m14 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m15 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // ===== ROUND 1 ===== Schedule: [2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8]
  s0 = (s0 + s4 | 0) + m2 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m6 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m3 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m10 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m7 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m0 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m4 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m13 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  s0 = (s0 + s5 | 0) + m1 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m11 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m12 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m5 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m9 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m14 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m15 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m8 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // ===== ROUND 2 ===== Schedule: [3,4,10,12,13,2,7,14,6,5,9,0,11,15,8,1]
  s0 = (s0 + s4 | 0) + m3 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m4 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m10 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m12 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m13 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m2 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m7 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m14 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  s0 = (s0 + s5 | 0) + m6 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m5 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m9 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m0 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m11 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m15 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m8 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m1 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // ===== ROUND 3 ===== Schedule: [10,7,12,9,14,3,13,15,4,0,11,2,5,8,1,6]
  s0 = (s0 + s4 | 0) + m10 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m7 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m12 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m9 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m14 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m3 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m13 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m15 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  s0 = (s0 + s5 | 0) + m4 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m0 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m11 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m2 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m5 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m8 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m1 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m6 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // ===== ROUND 4 ===== Schedule: [12,13,9,11,15,10,14,8,7,2,5,3,0,1,6,4]
  s0 = (s0 + s4 | 0) + m12 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m13 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m9 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m11 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m15 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m10 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m14 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m8 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  s0 = (s0 + s5 | 0) + m7 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m2 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m5 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m3 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m0 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m1 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m6 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m4 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // ===== ROUND 5 ===== Schedule: [9,14,11,5,8,12,15,1,13,3,0,10,2,6,4,7]
  s0 = (s0 + s4 | 0) + m9 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m14 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m11 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m5 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m8 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m12 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m15 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m1 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  s0 = (s0 + s5 | 0) + m13 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m3 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m0 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m10 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m2 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m6 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m4 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m7 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // ===== ROUND 6 ===== Schedule: [11,15,5,0,1,9,8,6,14,10,2,12,3,4,7,13]
  s0 = (s0 + s4 | 0) + m11 | 0; s12 ^= s0; s12 = (s12 >>> 16) | (s12 << 16);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 12) | (s4 << 20);
  s0 = (s0 + s4 | 0) + m15 | 0; s12 ^= s0; s12 = (s12 >>> 8) | (s12 << 24);
  s8 = s8 + s12 | 0; s4 ^= s8; s4 = (s4 >>> 7) | (s4 << 25);

  s1 = (s1 + s5 | 0) + m5 | 0; s13 ^= s1; s13 = (s13 >>> 16) | (s13 << 16);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 12) | (s5 << 20);
  s1 = (s1 + s5 | 0) + m0 | 0; s13 ^= s1; s13 = (s13 >>> 8) | (s13 << 24);
  s9 = s9 + s13 | 0; s5 ^= s9; s5 = (s5 >>> 7) | (s5 << 25);

  s2 = (s2 + s6 | 0) + m1 | 0; s14 ^= s2; s14 = (s14 >>> 16) | (s14 << 16);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 12) | (s6 << 20);
  s2 = (s2 + s6 | 0) + m9 | 0; s14 ^= s2; s14 = (s14 >>> 8) | (s14 << 24);
  s10 = s10 + s14 | 0; s6 ^= s10; s6 = (s6 >>> 7) | (s6 << 25);

  s3 = (s3 + s7 | 0) + m8 | 0; s15 ^= s3; s15 = (s15 >>> 16) | (s15 << 16);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 12) | (s7 << 20);
  s3 = (s3 + s7 | 0) + m6 | 0; s15 ^= s3; s15 = (s15 >>> 8) | (s15 << 24);
  s11 = s11 + s15 | 0; s7 ^= s11; s7 = (s7 >>> 7) | (s7 << 25);

  s0 = (s0 + s5 | 0) + m14 | 0; s15 ^= s0; s15 = (s15 >>> 16) | (s15 << 16);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 12) | (s5 << 20);
  s0 = (s0 + s5 | 0) + m10 | 0; s15 ^= s0; s15 = (s15 >>> 8) | (s15 << 24);
  s10 = s10 + s15 | 0; s5 ^= s10; s5 = (s5 >>> 7) | (s5 << 25);

  s1 = (s1 + s6 | 0) + m2 | 0; s12 ^= s1; s12 = (s12 >>> 16) | (s12 << 16);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 12) | (s6 << 20);
  s1 = (s1 + s6 | 0) + m12 | 0; s12 ^= s1; s12 = (s12 >>> 8) | (s12 << 24);
  s11 = s11 + s12 | 0; s6 ^= s11; s6 = (s6 >>> 7) | (s6 << 25);

  s2 = (s2 + s7 | 0) + m3 | 0; s13 ^= s2; s13 = (s13 >>> 16) | (s13 << 16);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 12) | (s7 << 20);
  s2 = (s2 + s7 | 0) + m4 | 0; s13 ^= s2; s13 = (s13 >>> 8) | (s13 << 24);
  s8 = s8 + s13 | 0; s7 ^= s8; s7 = (s7 >>> 7) | (s7 << 25);

  s3 = (s3 + s4 | 0) + m7 | 0; s14 ^= s3; s14 = (s14 >>> 16) | (s14 << 16);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 12) | (s4 << 20);
  s3 = (s3 + s4 | 0) + m13 | 0; s14 ^= s3; s14 = (s14 >>> 8) | (s14 << 24);
  s9 = s9 + s14 | 0; s4 ^= s9; s4 = (s4 >>> 7) | (s4 << 25);

  // Output
  if (!truncate) {
    out[outOff + 8 | 0] = (s8 ^ cv[cvOff]) | 0;
    out[outOff + 9 | 0] = (s9 ^ cv[cvOff + 1 | 0]) | 0;
    out[outOff + 10 | 0] = (s10 ^ cv[cvOff + 2 | 0]) | 0;
    out[outOff + 11 | 0] = (s11 ^ cv[cvOff + 3 | 0]) | 0;
    out[outOff + 12 | 0] = (s12 ^ cv[cvOff + 4 | 0]) | 0;
    out[outOff + 13 | 0] = (s13 ^ cv[cvOff + 5 | 0]) | 0;
    out[outOff + 14 | 0] = (s14 ^ cv[cvOff + 6 | 0]) | 0;
    out[outOff + 15 | 0] = (s15 ^ cv[cvOff + 7 | 0]) | 0;
  }

  out[outOff] = (s0 ^ s8) | 0;
  out[outOff + 1 | 0] = (s1 ^ s9) | 0;
  out[outOff + 2 | 0] = (s2 ^ s10) | 0;
  out[outOff + 3 | 0] = (s3 ^ s11) | 0;
  out[outOff + 4 | 0] = (s4 ^ s12) | 0;
  out[outOff + 5 | 0] = (s5 ^ s13) | 0;
  out[outOff + 6 | 0] = (s6 ^ s14) | 0;
  out[outOff + 7 | 0] = (s7 ^ s15) | 0;
}


// ============================================================================
// compress4x: 4-way i32x4 SIMD compression, generated as a WASM module on load.
// Memory layout (v128 slots): $0..$15 = message words, $16..$31 = state.
// In the Uint32Array view: message word w at index w*4 (+lane), state word k at
// index (16+k)*4 (+lane). compress4x reads both regions, runs the 7 rounds, and
// writes the 8 output chaining-value words back over $16..$23.
// ============================================================================
const { compress4x, wasmU32 } = (function () {
  const code = new Uint8Array(16384);
  let n = 0;
  const put = (a) => { for (let i = 0; i < a.length; i++) code[n++] = a[i]; };
  const writeLeb5 = (v, pos) => { for (let i = 0; i < 5; i++) { code[pos + i] = (v & 127) | (i < 4 ? 0x80 : 0); v >>= 7; } };
  const leb = (v) => { v |= 0; const r = []; for (;;) { const b = v & 0x7f; v >>= 7; if ((v === 0 && (b & 0x40) === 0) || (v === -1 && (b & 0x40) !== 0)) { r.push(b); return r; } r.push(b | 0x80); } };

  put([
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // magic + version
    0x01, 0x04, 0x01, 0x60, 0x00, 0x00,             // Types: T0 () -> ()
    0x02, 0x0b, 0x01, 0x02, 0x6a, 0x73, 0x03, 0x6d, 0x65, 0x6d, 0x02, 0x00, 0x01, // Imports: js.mem (min 1)
    0x03, 0x02, 0x01, 0x00,                         // Functions: [T0]
    0x07, 0x0e, 0x01,                               // Exports: 1
    0x0a, 0x63, 0x6f, 0x6d, 0x70, 0x72, 0x65, 0x73, 0x73, 0x34, 0x78, 0x00, 0x00, // "compress4x" funcidx 0
    0x0a, 0x00, 0x00, 0x00, 0x00, 0x00,             // Code section: reserved size (5 bytes)
    0x01,                                           // 1 code entry
    0x00, 0x00, 0x00, 0x00, 0x00,                   // reserved func body size (5 bytes)
    0x01, 0x20, 0x7b,                               // locals: 32 x v128
  ]);
  const body = n;

  for (let i = 0; i < 32; i++) put([0x41, ...leb(i * 16), 0xfd, 0, 4, 0, 0x21, i]); // local $i = i128.load[i*16]

  const M = [
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2, 6, 3, 10, 7, 0, 4,
    13, 1, 11, 12, 5, 9, 14, 15, 8, 3, 4, 10, 12, 13, 2, 7, 14, 6, 5, 9, 0, 11,
    15, 8, 1, 10, 7, 12, 9, 14, 3, 13, 15, 4, 0, 11, 2, 5, 8, 1, 6, 12, 13, 9,
    11, 15, 10, 14, 8, 7, 2, 5, 3, 0, 1, 6, 4, 9, 14, 11, 5, 8, 12, 15, 1, 13,
    3, 0, 10, 2, 6, 4, 7, 11, 15, 5, 0, 1, 9, 8, 6, 14, 10, 2, 12, 3, 4, 7, 13,
  ];
  let mi = 0;
  // rotr by 16 and by 8 are byte permutations -> one i8x16.shuffle (0xfd 0x0d)
  // instead of shr_u + shl + v128.or. Per i32 lane: rotr16 = bytes [2,3,0,1],
  // rotr8 = bytes [1,2,3,0]; tiled across the 4 lanes of the v128.
  const SHUF16 = [2, 3, 0, 1, 6, 7, 4, 5, 10, 11, 8, 9, 14, 15, 12, 13];
  const SHUF8 = [1, 2, 3, 0, 5, 6, 7, 4, 9, 10, 11, 8, 13, 14, 15, 12];
  const gi = (a, b, c, d, dRot, bRot) => {
    const m = M[mi++];
    const dShuf = dRot === 16 ? SHUF16 : SHUF8; // dRot is always 16 or 8
    put([
      0x20, a, 0x20, m, 0xfd, 174, 1, 0xfd, 174, 1, 0x22, a, // s[a]=s[a]+s[m]+s[b]; (b loaded outside)
      0x20, d, 0xfd, 81, 0x22, d,                            // s[d]^=s[a]
      0x20, d, 0xfd, 0x0d, ...dShuf, 0x22, d,                // s[d]=rotr(dRot) via i8x16.shuffle
      0x20, c, 0xfd, 174, 1, 0x22, c,                        // s[c]+=s[d]
      0x20, b, 0xfd, 81, 0x22, b,                            // s[b]^=s[c]
      0x41, bRot, 0xfd, 173, 1, 0x20, b, 0x41, 32 - bRot, 0xfd, 171, 1, 0xfd, 80, // s[b]=rotr(bRot)
    ]);
  };
  const g = (a, b, c, d) => { put([0x20, b]); gi(a, b, c, d, 16, 12); put([0x22, b]); gi(a, b, c, d, 8, 7); put([0x21, b]); };
  for (let r = 0; r < 7; r++) {
    g(16, 20, 24, 28); g(17, 21, 25, 29); g(18, 22, 26, 30); g(19, 23, 27, 31); // columns
    g(16, 21, 26, 31); g(17, 22, 27, 28); g(18, 23, 24, 29); g(19, 20, 25, 30); // diagonals
  }
  for (let i = 16; i < 24; i++) put([0x41, ...leb(i * 16), 0x20, i, 0x20, i + 8, 0xfd, 81, 0xfd, 11, 4, 0]); // store s[i]^s[i+8]

  put([0x0b]); // end
  const len = n - body + 3;
  writeLeb5(len, body - 8);      // func body size
  writeLeb5(len + 6, body - 14); // code section size

  const memory = new WebAssembly.Memory({ initial: 1 });
  const inst = new WebAssembly.Instance(new WebAssembly.Module(code.subarray(0, n)), { js: { mem: memory } });
  return { compress4x: inst.exports.compress4x, wasmU32: new Uint32Array(memory.buffer) };
})();


// ============================================================================
// hash(input): SIMD bulk over whole groups of 4 chunks, scalar for the tail.
// ============================================================================
function hash(input) {
  const length = input.length | 0;

  // Aligned 32-bit view for zero-copy transposition (little-endian only).
  let words = null;
  if (IS_LITTLE_ENDIAN) {
    let bytes = input;
    if ((input.byteOffset & 3) !== 0) bytes = input.slice();
    words = new Uint32Array(bytes.buffer, bytes.byteOffset, length >> 2);
  }

  const maxDepth = (Math.ceil(Math.log2((length / CHUNK_LEN | 0) + 2)) + 4) | 0;
  const stack = ensureCvStack(maxDepth);
  let stackPos = 0;
  let chunkCounter = 0;
  let offset = 0;

  // ---- SIMD bulk: whole 4-chunk (4096-byte) groups, leaving >=1 byte for the tail ----
  const fourGroupEnd = length > 0 ? (((length - 1) / 4096) | 0) * 4096 : 0;
  let w = 0; // word cursor into `words`
  while (offset < fourGroupEnd) {
    for (let i = 0; i < 8; i++) {                 // broadcast IV to the 4 lanes' running CV
      const c = IV[i], s = (16 + i) * 4;
      wasmU32[s] = c; wasmU32[s + 1] = c; wasmU32[s + 2] = c; wasmU32[s + 3] = c;
    }
    for (let blk = 0; blk < 16; blk++) {
      for (let i = 0; i < 64; i += 4, w++) {      // transpose: lane j = chunk j's word
        wasmU32[i] = words[w];
        wasmU32[i + 1] = words[w + 256];
        wasmU32[i + 2] = words[w + 512];
        wasmU32[i + 3] = words[w + 768];
      }
      const flags = (blk === 0 ? CHUNK_START : 0) | (blk === 15 ? CHUNK_END : 0);
      for (let i = 0; i < 4; i++) {
        wasmU32[96 + i] = 0x6a09e667; wasmU32[100 + i] = 0xbb67ae85;
        wasmU32[104 + i] = 0x3c6ef372; wasmU32[108 + i] = 0xa54ff53a;
        wasmU32[112 + i] = (chunkCounter + i) | 0;
        wasmU32[116 + i] = ((chunkCounter + i) / 0x100000000) | 0;
        wasmU32[120 + i] = BLOCK_LEN; wasmU32[124 + i] = flags;
      }
      compress4x();
    }
    for (let c = 0; c < 4; c++) {                 // pull the 4 chunk CVs off the lanes
      for (let i = 0; i < 8; i++) stack[stackPos + i] = wasmU32[(16 + i) * 4 + c];
      stackPos += 8;
    }
    // merge the 4-chunk subtree into one CV: ((c0,c1),(c2,c3))
    compress(IV, 0, stack, stackPos - 32, stack, stackPos - 32, 0, BLOCK_LEN, PARENT, true);
    compress(IV, 0, stack, stackPos - 16, stack, stackPos - 24, 0, BLOCK_LEN, PARENT, true);
    compress(IV, 0, stack, stackPos - 32, stack, stackPos - 32, 0, BLOCK_LEN, PARENT, true);
    stackPos -= 24;

    chunkCounter += 4;
    offset += 4096;
    w += 768;

    // merge completed 4-chunk subtrees by the trailing zeros of the group index
    let groups = chunkCounter >> 2;
    while ((groups & 1) === 0) {
      stackPos -= 16;
      compress(IV, 0, stack, stackPos, stack, stackPos, 0, BLOCK_LEN, PARENT, true);
      stackPos += 8;
      groups >>= 1;
    }
  }

  // ---- remaining whole chunks (scalar), still leaving >=1 byte for the tail ----
  const fullChunksEnd = offset + Math.max(0, ((length - offset - 1) | 1023) - 1023);
  while (offset < fullChunksEnd) {
    stack.set(IV, stackPos);
    for (let i = 0; i < 16; i++, offset += 64) {
      const f = (i === 0 ? CHUNK_START : 0) | (i === 15 ? CHUNK_END : 0);
      if (words !== null) {
        compress(stack, stackPos, words, offset >> 2, stack, stackPos, chunkCounter, BLOCK_LEN, f, true);
      } else {
        readWordsLE(input, offset, blockWords, 16);
        compress(stack, stackPos, blockWords, 0, stack, stackPos, chunkCounter, BLOCK_LEN, f, true);
      }
    }
    chunkCounter += 1;
    stackPos += 8;
    let total = chunkCounter;
    while ((total & 1) === 0) {
      stackPos -= 16;
      compress(IV, 0, stack, stackPos, stack, stackPos, 0, BLOCK_LEN, PARENT, true);
      stackPos += 8;
      total >>= 1;
    }
  }

  // ---- final chunk: full blocks then the last (possibly partial) block + ROOT ----
  const numFullBlocks = length > 0 ? (((length - offset - 1) / BLOCK_LEN) | 0) : 0;
  stack.set(IV, stackPos);
  for (let i = 0; i < numFullBlocks; i++, offset += 64) {
    const f = (i === 0 ? CHUNK_START : 0);
    if (words !== null && (offset + BLOCK_LEN) <= (length & ~3)) {
      compress(stack, stackPos, words, offset >> 2, stack, stackPos, chunkCounter, BLOCK_LEN, f, true);
    } else {
      readWordsLE(input, offset, blockWords, 16);
      compress(stack, stackPos, blockWords, 0, stack, stackPos, chunkCounter, BLOCK_LEN, f, true);
    }
  }
  const lastLen = length - offset | 0;
  const isFirst = numFullBlocks === 0;
  const lastFlags = (isFirst ? CHUNK_START : 0) | CHUNK_END;
  readPartialBlock(input, offset, lastLen, blockWords);

  if (stackPos === 0) {
    compress(stack, 0, blockWords, 0, outWords, 0, chunkCounter, lastLen, lastFlags | ROOT, true);
    return wordsToBytes(outWords);
  }
  compress(stack, stackPos, blockWords, 0, stack, stackPos, chunkCounter, lastLen, lastFlags, true);
  stackPos += 8;
  while (stackPos > 16) {
    stackPos -= 16;
    compress(IV, 0, stack, stackPos, stack, stackPos, 0, BLOCK_LEN, PARENT, true);
    stackPos += 8;
  }
  stackPos -= 16;
  compress(IV, 0, stack, stackPos, outWords, 0, 0, BLOCK_LEN, PARENT | ROOT, true);
  return wordsToBytes(outWords);
}

function wordsToBytes(words) {
  const result = new Uint8Array(32);
  for (let i = 0; i < 8; i = i + 1 | 0) {
    const w = words[i] | 0;
    const j = i << 2;
    result[j] = w & 0xff;
    result[j + 1 | 0] = (w >>> 8) & 0xff;
    result[j + 2 | 0] = (w >>> 16) & 0xff;
    result[j + 3 | 0] = (w >>> 24) & 0xff;
  }
  return result;
}

function toHex(bytes) {
  let s = '';
  for (let i = 0; i < bytes.length; i++) {
    s += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
  }
  return s;
}

if (typeof module !== 'undefined' && module.exports) {
  module.exports = { hash, toHex };
}

// ============================================================================
// Self-test + benchmark - runs only when executed directly.
// ============================================================================
if (typeof require !== 'undefined' && require.main === module) {
  console.log('BLAKE3 SIMD - WASM compress4x (generated on load, no .wasm shipped)');
  console.log('='.repeat(64));

  function genInput(n) { const a = new Uint8Array(n); for (let i = 0; i < n; i++) a[i] = i % 251; return a; }
  // Verify against the bundled official vectors (all 35, hash mode).
  let allPass = true;
  try {
    const tv = require('./test_vectors.json');
    let pass = 0;
    for (const c of tv.cases) {
      if (toHex(hash(genInput(c.input_len))) === c.hash.slice(0, 64)) pass++;
      else allPass = false;
    }
    console.log(`Official vectors (hash mode): ${pass}/${tv.cases.length} ${allPass ? 'PASS' : 'FAIL'}`);
  } catch (e) {
    console.log('test_vectors.json not found - skipping conformance');
  }
  if (!allPass) { console.log('TESTS FAILED - aborting benchmark'); process.exit(1); }

  console.log('\nBenchmark (warming up JIT)...');
  const warm = new Uint8Array(64 * 1024).map((_, i) => i & 0xff);
  for (let i = 0; i < 3000; i++) hash(warm);

  const sizes = [[1024, '1 KiB', 20000], [65536, '64 KiB', 3000],
                 [1048576, '1 MiB', 300], [10485760, '10 MiB', 30]];
  for (const [size, label, iters] of sizes) {
    const data = new Uint8Array(size).map((_, i) => i & 0xff);
    for (let i = 0; i < 5; i++) hash(data);
    const t0 = process.hrtime.bigint();
    for (let i = 0; i < iters; i++) hash(data);
    const sec = Number(process.hrtime.bigint() - t0) / 1e9;
    const mib = (size * iters) / sec / (1024 * 1024);
    console.log(`${label.padStart(8)}: ${mib.toFixed(1).padStart(8)} MiB/s (${(mib / 1024).toFixed(3)} GiB/s)`);
  }
}
