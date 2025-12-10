'use strict';

// ============================================================================
// BLAKE3 ULTRA - Maximum Performance Pure JavaScript Implementation
// ============================================================================
// Key optimizations:
// 1. FULLY UNROLLED 7 rounds - NO loop overhead
// 2. PRECOMPUTED message schedule - NO permutation operations (saves 108 assignments)
// 3. Zero-copy little-endian path
// 4. Pre-allocated buffers
// 5. Offset-based compress
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

// ============================================================================
// FULLY UNROLLED COMPRESS - All 7 rounds with precomputed message schedule
// Message schedule per round:
// R0: [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]
// R1: [2,6,3,10,7,0,4,13,1,11,12,5,9,14,15,8]
// R2: [3,4,10,12,13,2,7,14,6,5,9,0,11,15,8,1]
// R3: [10,7,12,9,14,3,13,15,4,0,11,2,5,8,1,6]
// R4: [12,13,9,11,15,10,14,8,7,2,5,3,0,1,6,4]
// R5: [9,14,11,5,8,12,15,1,13,3,0,10,2,6,4,7]
// R6: [11,15,5,0,1,9,8,6,14,10,2,12,3,4,7,13]
// ============================================================================
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

function hash(input) {
  const length = input.length | 0;

  let inputWords = null;
  const canZeroCopy = IS_LITTLE_ENDIAN &&
                      ((input.byteOffset & 3) === 0) &&
                      (length >= 64);

  if (canZeroCopy) {
    try {
      inputWords = new Uint32Array(input.buffer, input.byteOffset, length >> 2);
    } catch (e) {
      inputWords = null;
    }
  }

  const numChunks = Math.ceil(length / CHUNK_LEN) || 1;
  const maxDepth = (Math.ceil(Math.log2(numChunks + 1)) + 2) | 0;
  const stack = ensureCvStack(maxDepth);

  let stackPos = 0;
  let chunkCounter = 0;
  let offset = 0;

  const fullChunksEnd = length > 0 ? (Math.floor((length - 1) / CHUNK_LEN) * CHUNK_LEN) | 0 : 0;

  while (offset < fullChunksEnd) {
    stack.set(IV, stackPos);

    for (let block = 0; block < 16; block = block + 1 | 0) {
      const blockFlags = (block === 0 ? CHUNK_START : 0) |
                         (block === 15 ? CHUNK_END : 0);

      if (inputWords !== null) {
        compress(stack, stackPos, inputWords, offset >> 2, stack, stackPos,
                 chunkCounter, BLOCK_LEN, blockFlags, true);
      } else {
        readWordsLE(input, offset, blockWords, 16);
        compress(stack, stackPos, blockWords, 0, stack, stackPos,
                 chunkCounter, BLOCK_LEN, blockFlags, true);
      }
      offset = offset + BLOCK_LEN | 0;
    }

    chunkCounter = chunkCounter + 1 | 0;
    stackPos = stackPos + 8 | 0;

    let total = chunkCounter | 0;
    while ((total & 1) === 0) {
      stackPos = stackPos - 16 | 0;
      compress(IV, 0, stack, stackPos, stack, stackPos, 0, BLOCK_LEN, PARENT, true);
      stackPos = stackPos + 8 | 0;
      total = total >> 1;
    }
  }

  const remaining = length - offset | 0;

  if (remaining > 0 || length === 0) {
    stack.set(IV, stackPos);

    const numFullBlocks = remaining > 0 ? ((remaining - 1) / BLOCK_LEN) | 0 : 0;

    for (let block = 0; block < numFullBlocks; block = block + 1 | 0) {
      const blockFlags = (block === 0 ? CHUNK_START : 0);

      if (inputWords !== null && (offset + BLOCK_LEN) <= (length & ~3)) {
        compress(stack, stackPos, inputWords, offset >> 2, stack, stackPos,
                 chunkCounter, BLOCK_LEN, blockFlags, true);
      } else {
        readWordsLE(input, offset, blockWords, 16);
        compress(stack, stackPos, blockWords, 0, stack, stackPos,
                 chunkCounter, BLOCK_LEN, blockFlags, true);
      }
      offset = offset + BLOCK_LEN | 0;
    }

    const lastBlockLen = length - offset | 0;
    const isFirstBlock = numFullBlocks === 0;
    const lastFlags = (isFirstBlock ? CHUNK_START : 0) | CHUNK_END;

    readPartialBlock(input, offset, lastBlockLen, blockWords);

    if (stackPos === 0) {
      compress(stack, 0, blockWords, 0, outWords, 0,
               chunkCounter, lastBlockLen, lastFlags | ROOT, true);
      return wordsToBytes(outWords);
    }

    compress(stack, stackPos, blockWords, 0, stack, stackPos,
             chunkCounter, lastBlockLen, lastFlags, true);
    stackPos = stackPos + 8 | 0;
  }

  while (stackPos > 16) {
    stackPos = stackPos - 16 | 0;
    compress(IV, 0, stack, stackPos, stack, stackPos, 0, BLOCK_LEN, PARENT, true);
    stackPos = stackPos + 8 | 0;
  }

  stackPos = stackPos - 16 | 0;
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

// ============================================================================
// TEST & BENCHMARK
// ============================================================================

console.log('BLAKE3 ULTRA - Fully Unrolled Node.js Benchmark');
console.log('='.repeat(60));
console.log(`Endianness: ${IS_LITTLE_ENDIAN ? 'Little (zero-copy enabled)' : 'Big (fallback)'}`);
console.log();

// Test vectors
console.log('Test Vectors:');
function genInput(n) {
  const a = new Uint8Array(n);
  for (let i = 0; i < n; i++) a[i] = i % 251;
  return a;
}

const tests = [
  [0, 'af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262'],
  [1, '2d3adedff11b61f14c886e35afa036736dcd87a74d27b5c1510225d0f592e213'],
  [64, '4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98'],
  [1024, '42214739f095a406f3fc83deb889744ac00df831c10daa55189b5d121c855af7'],
  [1025, 'd00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444'],
];

let allPass = true;
for (const [len, expected] of tests) {
  const result = toHex(hash(genInput(len)));
  const pass = result === expected;
  if (!pass) allPass = false;
  console.log(`  len=${String(len).padStart(5)}: ${pass ? 'PASS' : 'FAIL'}`);
  if (!pass) {
    console.log(`    Expected: ${expected}`);
    console.log(`    Got:      ${result}`);
  }
}

console.log();

if (!allPass) {
  console.log('TESTS FAILED - aborting benchmark');
  process.exit(1);
}

// Benchmark
console.log('Benchmark:');
console.log('Warming up JIT (this takes longer for better optimization)...');

const warmupData = new Uint8Array(1024 * 1024);
for (let i = 0; i < warmupData.length; i++) warmupData[i] = i & 0xff;

// Extended warmup for better JIT optimization
for (let i = 0; i < 10000; i++) hash(warmupData);

console.log('Running benchmarks...\n');

const sizes = [
  [1024, '1 KiB', 10000],
  [64 * 1024, '64 KiB', 2000],
  [1024 * 1024, '1 MiB', 200],
  [10 * 1024 * 1024, '10 MiB', 20],
  [100 * 1024 * 1024, '100 MiB', 5],
];

for (const [size, label, iterations] of sizes) {
  const data = new Uint8Array(size);
  for (let i = 0; i < size; i++) data[i] = i & 0xff;

  // Warmup for this size
  for (let i = 0; i < 5; i++) hash(data);

  const start = process.hrtime.bigint();
  for (let i = 0; i < iterations; i++) {
    hash(data);
  }
  const end = process.hrtime.bigint();

  const totalBytes = size * iterations;
  const totalNs = Number(end - start);
  const totalSec = totalNs / 1e9;
  const mibPerSec = totalBytes / totalSec / (1024 * 1024);
  const gibPerSec = mibPerSec / 1024;

  console.log(`${label.padStart(8)}: ${mibPerSec.toFixed(1).padStart(8)} MiB/s (${gibPerSec.toFixed(3)} GiB/s)`);
}

console.log();
console.log('Note: Browser (Chrome) typically performs 20-50% better than Node.js');
