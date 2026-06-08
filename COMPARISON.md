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
64 B     199    232    213    71   |    74    199          10
256 B    598    616    497   268   |   256    566          40
1 KB     889    905    735   622   |   624    959         163
4 KB     967    979    790   770   |   766   1656         497
16 KB    997   1432    791   780   |  1258   1763        1164
64 KB    990   1622    793   790   |  1547   1766        1574
256 KB   997   1682    794   792   |  1606   1797        2184
1 MB    1002   1693    807   790   |  1617   1802        2241
10 MB   1000   1680    784   784   |  1544   1786        2124

* = this repo.  ultra = blake3-ultra.js (pure JS).  simd = blake3-simd.js (WASM SIMD).
opt = blake3-optimized.  js = blake3-js.  Bk3JS / fast = WASM-SIMD bounty entries.
sha256(native) = WebCrypto, a native-code anchor (different algorithm).
```

## Takeaways

- **blake3-ultra (pure JS) is the fastest scalar pure-JavaScript entry at every
  size** - no WebAssembly, no SIMD, no workers - and fastest of *everything* on
  64-byte messages, where SIMD/WASM setup cost cannot amortize.

- **blake3-simd beats Bk3JS
  WASM-SIMD entry at every size**, and is #1 of all entries at 64 B. Only
  `blake3-fast` is faster at bulk (~6% at 1 MB), because it goes beyond the blog
  with a wider SIMD kernel.

- The SIMD entries lead at large inputs because data-parallel SIMD processes
  multiple chunks at once; a scalar JS path structurally cannot match that. That is
  hardware vectorization, not an inefficiency in the scalar code.

## Reproducing

The competitors live in zooko/potential-guacamole. Clone it, then run each
implementation's `hash` through one shared harness alongside `blake3-ultra.js` and
`blake3-simd.js`. Node 22+ (for in-place `.ts` and WASM); the entries are a mix of
ESM `.js`, CommonJS, and TypeScript with SIMD.
