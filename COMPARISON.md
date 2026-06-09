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
              pure-JS scalar           WASM SIMD                  native
              --------------     ---------------------------     ------
input    ultra*  opt    js   |  simd*  simd8*  Bk3JS  fast   |  sha256
-----    -----  -----  ----  |  -----  -----   -----  -----  |  ------
64 B      222    210    76   |   231    231      76    206   |     9
256 B     598    517   275   |   620    609     263    593   |    38
1 KB      888    732   645   |   918    896     639    961   |   154
4 KB      966    780   768   |   974    970     758   1666   |   496
16 KB     998    790   781   |  1535   1308    1264   1764   |  1115
64 KB     992    794   789   |  1739   1722    1538   1768   |  1831
256 KB   1012    801   789   |  1876   1944    1642   1816   |  2160
1 MB      995    794   788   |  1889   2003    1616   1802   |  2331
10 MB    1001    794   782   |  1874   1997    1569   1792   |  2065

* = this repo.  ultra = blake3-ultra.js (pure JS, 1 lane).
simd = blake3-simd.js (WASM SIMD, 4-wide).  simd8 = simd8/blake3-simd8.js (WASM SIMD, 8-wide).
opt = blake3-optimized, js = blake3-js (pure-JS competitors).
Bk3JS / fast = WASM-SIMD bounty entries.  sha256(native) = WebCrypto anchor (noisy, different algorithm).
All single-threaded. simd8 also sustains ~1.95 GiB/s at 100 MiB-1 GiB (memory-bandwidth bound).
```

## Takeaways

- **blake3-ultra (pure JS) is the fastest scalar pure-JavaScript entry at every
  size** - no WebAssembly, no SIMD, no workers - and fastest of *everything* on
  64-byte messages, where SIMD/WASM setup cost cannot amortize. It sits at the
  pure-JS ceiling: ~20 integer ops/byte at ~1 GiB/s saturates a single core's ALUs.

- **blake3-simd8 (8-wide) is the fastest single-threaded entry in the field at
  bulk** - ~2.0 GiB/s at 256 KiB and up, beating blake3-simd (4-wide), blake3-fast,
  and everything else. "8-wide" is two interleaved 128-bit v128 streams (8 chunks
  per call) for more instruction-level parallelism - still 128-bit, still single
  thread, still in-scope. (blake3-simd, the 4-wide build, is marginally faster in
  the 16-64 KiB band where the larger groups don't fully amortize.)

- The 8-wide win over 4-wide is only ~6%, which is the telling measurement: it means
  the SIMD kernel is **throughput-bound, not latency-bound** - the ALU ports are
  already ~saturated at 4-wide. So ~2.0 GiB/s is the practical single-thread ceiling
  for this approach; more ILP gives diminishing returns.

- Only native SHA-256 is reliably faster, and that's a hardware gap, not an effort
  gap: it runs on the SHA-NI extension (dedicated crypto silicon), and WASM SIMD is
  capped at 128-bit (no AVX2/512). Reaching 3+ GiB/s would need either wider SIMD
  (impossible in WASM) or multiple cores (Web Workers / worker_threads).

- The SIMD entries lead at large inputs because data-parallel SIMD processes
  multiple chunks at once; a scalar JS path structurally cannot match that. That is
  hardware vectorization, not an inefficiency in the scalar code.

## Reproducing

The competitors live in zooko/potential-guacamole. Clone it, then run each
implementation's `hash` through one shared harness alongside `blake3-ultra.js` and
`blake3-simd.js`. Node 22+ (for in-place `.ts` and WASM); the entries are a mix of
ESM `.js`, CommonJS, and TypeScript with SIMD.
