# Blake3-JavaScript
A high performance pure JavaScript implementation of the BLAKE3 cryptographic hash function optimized for browser environments.

  ## Performance

  - .9~1.0 GiB/s on modern browsers
  - 100% pure JavaScript no WebAssembly, no SIMD, no Web Workers
  - Tested on Intel Core i7-14700K

  ## Features

  - Fully unrolled 7 round compression function
  - Zero-copy path for aligned little endian data
  - Pre allocated buffers to minimize GC pressure
  - Extended JIT warmup for consistent benchmarks
  - Passes all official BLAKE3 test vectors
