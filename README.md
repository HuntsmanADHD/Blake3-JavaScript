# Blake3-JavaScript
A high performance pure JavaScript implementation of the BLAKE3 cryptographic hash function optimized for browser environments.

  ## Performance

  - .9~1.0 GiB/s on modern browsers
  - 100% pure JavaScript no WebAssembly, no SIMD, no Web Workers
  - ~8x faster than @noble/hashes BLAKE3 in pure JS
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

  ## Testing

  - `npm test` runs the official test vectors, 35 lengths x 3 modes x 32 byte and full XOF output
  - `npm run bench` runs the Node throughput benchmark
  - `npm run bench:compare` runs a head to head against @noble/hashes and native SHA
