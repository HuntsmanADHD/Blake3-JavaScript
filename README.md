# Blake3-JavaScript
A high performance pure JavaScript implementation of the BLAKE3 cryptographic hash function optimized for browser environments.

  ## Performance

  - .9~1.0 GiB/s on modern browsers 100% pure JavaScript no WebAssembly, no SIMD, no Web Workers
  - ~8x faster than @noble/hashes BLAKE3 in pure JS
  - Fastest scalar pure JS entry in the BLAKE3 bounty field, see COMPARISON.md
  - Optional WASM SIMD build reaches ~1.9 GiB/s, fastest JS+WASM entry in the field, see below
  - Tested on Intel Core i7-14700K

  ## Features

  - Fully unrolled 7 round compression function
  - Zero-copy path for aligned little endian data
  - Pre allocated buffers to minimize GC pressure
  - Extended JIT warmup for consistent benchmarks
  - All three modes hash, keyed_hash, derive_key
  - Extendable output XOF for arbitrary length digests
  - Passes all official BLAKE3 test vectors across every mode

  ## Usage

  ```js
  const { hash, keyedHash, deriveKey, hashXOF, toHex } = require('./blake3-ultra.js');

  toHex(hash(new TextEncoder().encode('hello')));   // 32 byte digest
  keyedHash(key32, data);                           // MAC, key is 32 bytes
  deriveKey('app v1 context', keyMaterial);         // key derivation
  hashXOF(data, 131);                               // 131 byte extended output
  ```

  Importing the module does not run the benchmark. Run it directly for the
  Node benchmark, or open blake3-ultra-v2.html in a browser.

  ## Optional WASM SIMD build

  blake3-simd.js is a separate build that adds step 9 from the Fleek blog, a
  4 wide i32x4 compress4x generated as WebAssembly SIMD at load time. No .wasm
  file is shipped, the module is assembled from JS and compiled synchronously, so
  hash stays synchronous and it is still one file.

  - ~1.9 GiB/s on bulk input, fastest JS+WASM entry in the bounty field at every size
  - Kernel uses i8x16.shuffle for the 16 and 8 bit rotates, constant state words hoisted out of the block loop
  - Plain hash mode, 32 byte output only, little endian fast path with scalar fallback
  - Passes all 35 official hash mode vectors
  - WASM bytecode follows the Fleek blog, orchestration adapted from the Bk3JS entry
  - 4 wide v128 is ~2-4x narrower than native AVX2/AVX-512, so native SHA-NI SHA-256 stays ahead

  ```js
  const { hash, toHex } = require('./blake3-simd.js');
  toHex(hash(data));
  ```

  See COMPARISON.md for the full on-machine table against the bounty entries.

  ## Testing

  - `npm test` runs the official test vectors, 35 lengths x 3 modes x 32 byte and full XOF output
  - `npm run test:simd` verifies the WASM SIMD build against the 35 hash mode vectors
  - `npm run bench` runs the Node throughput benchmark
  - `npm run bench:simd` self-tests and benchmarks the WASM SIMD build
  - `npm run bench:compare` runs a head to head against @noble/hashes and native SHA
