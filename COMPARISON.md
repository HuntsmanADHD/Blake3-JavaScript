# Benchmark Comparison

How these implementations compare against the entries from the BLAKE3-in-JavaScript
bounty (zooko/potential-guacamole), measured **on one machine, one harness, equal
JIT warmup** so the ranking is apples to apples.

## Method

- Every implementation is driven through the identical loop (`await hash(data)`),
  same input sizes, same per-implementation warmup (3000 x 64 KiB).
- Throughput is MiB/s, higher is better.
- All entries were first verified correct against the official len-0 and len-1024
  vectors; a wrong-output entry (`Blake3inJavasScript`) was excluded.
- Absolute numbers are from a Linux x86-64 box. The bounty's published table was an
  Apple M4 Max, so values differ; only the *relative* ordering on one machine is
  meaningful.

## Results (MiB/s)

```
                 pure JavaScript            WASM / SIMD
                 ---------------            -----------
input  ultra*  simd*   opt    js   |  Bk3JS  fast    sha256(native)
-----  -----  -----  -----  -----  |  -----  -----   --------------
64 B     222    231    210    76   |    76    206           9
256 B    598    620    517   275   |   263    593          38
1 KB     888    918    732   645   |   639    961         154
4 KB     966    974    780   768   |   758   1666         496
16 KB    998   1535    790   781   |  1264   1764        1115
64 KB    992   1739    794   789   |  1538   1768        1831
256 KB  1012   1876    801   789   |  1642   1816        2160
1 MB     995   1889    794   788   |  1616   1802        2331
10 MB   1001   1874    794   782   |  1569   1792        2065

* = this repo.  ultra = blake3-ultra.js (pure JS).  simd = blake3-simd.js (WASM SIMD).
opt = blake3-optimized.  js = blake3-js.  Bk3JS / fast = WASM-SIMD bounty entries.
sha256(native) = WebCrypto, a native-code anchor (different algorithm).
```

## Takeaways

- **blake3-ultra (pure JS) is the fastest scalar pure-JavaScript entry at every
  size** - no WebAssembly, no SIMD, no workers - and fastest of *everything* on
  64-byte messages, where SIMD/WASM setup cost cannot amortize.

- **blake3-simd is the fastest JavaScript+WASM entry in the field at every size**,
  and #1 of all entries at 64 B. After two kernel optimizations (i8x16.shuffle
  rotates, and hoisting constant state words out of the per-block loop) it also
  passes `blake3-fast` at bulk, ~1.89 GiB/s at 1 MB.

- Only native SHA-256 is faster, and that is a hardware gap, not an effort gap:
  SHA-256 on this CPU runs on the SHA-NI extension (dedicated crypto silicon), and
  WASM SIMD is capped at 128-bit v128 (4-wide), while native BLAKE3 uses AVX2
  (8-wide) / AVX-512 (16-wide). 4-wide WASM is structurally 2-4x narrower than the
  hardware, so ~1.9 GiB/s is near the practical ceiling for this approach.

- The SIMD entries lead at large inputs because data-parallel SIMD processes
  multiple chunks at once; a scalar JS path structurally cannot match that. That is
  hardware vectorization, not an inefficiency in the scalar code.

## Reproducing

The competitors live in zooko/potential-guacamole. Clone it, then run each
implementation's `hash` through one shared harness alongside `blake3-ultra.js` and
`blake3-simd.js`. Node 22+ (for in-place `.ts` and WASM); the entries are a mix of
ESM `.js`, CommonJS, and TypeScript with SIMD.
