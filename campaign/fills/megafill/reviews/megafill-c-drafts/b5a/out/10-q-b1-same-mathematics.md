# 10 Q-B1: are UN's and U2-S's members the same mathematics?

| Other private | File:lines | Compared with | Same statement? | Same mathematics? |
|---|---|---|---|---|
| `un_step` | `Diagonalization/NTimeHierarchy` 255–274 | `ic_seam_step` | **Yes** (argument order and names aside: both give `seamCompTM`'s run to `c₃.mapState Sum.inr`, the `Sum.inr q₂` state and the inherited cut from `seamCompTM_run_ofCfg`/`_firstReturn_ofCfg`). The screen does not pair them: `un_step` is a term proof, `ic_seam_step` a tactic proof (v3 compares like with like) | yes |
| `un_step'` | same, 587–608 | `ic_seam_step` | no: the previous endpoint arrives relabelled (`c₂.mapState g`), collapsed by `Cfg.mapState_mapState` | a corollary of the same package |
| `un_canon_halt` | same, 276–322 | `ic_header_result` (first pass) | no: **exact** first halt at `3|pairEncode a b| + 4 + (4|a| + 5)` with liveness before (by `prefixCanon_run`/`_start` and `pairExtractTM_fst_run`), where R gives a **bounded** halt with output and head position (by `prefixCanon_complete`) | the same header pass, two contracts |
| `ss_capturedPrefix_run` (+ `ss_prefix_first_halt`, `ss_cleanCanonizer_first_halt`, `ss_capture_run`, `ss_capturedPrefix_fields`) | `UniversalK` 256–556 | `ic_header_capture` (+ `ic_capture_return`) | no: U2-S captures the prefix canonizer of a **general cleaned canonizer** `F` computing `f` in `τ` (exact first halt, silence ∀ u ≤ t, a space bound), R the pair extractors (bounded) | the same pattern (prefix pass captured by the returning embedding), generalized |
| `ss_capture_run` | `UniversalK` 369–397 | `ic_capture_return` | no: from an exact first halt with liveness, at the restarted `ss_captureTM` (`{ … with q₀ := … }`) via `initCfg_with_q₀`/`runFrom_with_q₀` and `ss_captureInitial`; R from a bounded halt via `exists_first_halt`, from an explicit start | the same transport |
| `ss_serialized_layout` | `UniversalK` 558–594 | `ic_layout_call` | no: source head at the **right end** (`(serializeK M).length`) and the summary as `fun p => bufferTape (unaryFin M.q₀) (p - 2)`; R's head at 0 and `summaryCells none (unaryFin M.q₀)` | the same specialization of `exists_seamLayoutTM` (its head-position parameter differs) |
| `ss_captureInitial` | `UniversalK` 324–362 | (none in R; B5a needs it) | — | the start identity B5a needs (out/11) |
| `xr_E_initCfg` | `ClassNP/ExhaustiveReplay` 3131–3150 | (B5a's start) | no (its own composite) | the same `initCfg_with_q₀` idiom |

So: one exact duplicate (`un_step` = `ic_seam_step`); the rest are the same constructions under
different contracts. Re-pointing UN to a published `seamCompTM_step` is mechanical (`un_step`'s
uses become `seamCompTM_step`, `un_step'` through it). Re-pointing U2-S needs adapters or a more
general public form (a head-position parameter for the layout call; the exact-first-halt form of
the capture), so it belongs to the dedup window, and `UniversalK` is U2's owned file in megafill C
anyway.
