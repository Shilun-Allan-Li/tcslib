# U2-S continuation 1 — final report

Outcome: **complete, proved modulo exactly `Turing.exists_seamLayoutTM` as authorized.**
All four phases are complete. `Turing.exists_selfStartupTMK` no longer has a `sorry`.

- Base: `6cfee54474e3d954e3395f9d9eab5d025452a8dd`.
- Branch: `fill/u2s-startup-cont1`.
- Final commit: `8e1aee0fc57a54b26678355396bda5922f71a49e`.
- Branch start: 2026-10-22T05:14:34.306136+00:00; end: 2026-10-22T06:14:22.325525+00:00.
- Initial campaign ancestor check passed. All five supplied attachment SHA-256 values matched;
  every normalized repository brief matched. First edit was exactly the supplied overlay with
  the single authorized `Build.SeamLayout` import.
- Checkpoints cp1, cp2 and cp3 were delivered immediately. This commit is checkpoint 4 and the
  final item delivery: `fill-u2s-startup-cont1-cp4.zip` and `fill-u2s-startup-cont1.zip`.
- No rebase, merge, cherry-pick, push, or out-of-region source edit was performed.

## Changes

The earlier checkpoints add the two required Proof sketches, restate `ss_capturedPrefix_run`
over the buffered composite, retain the cleaned canonizer's endpoint fields, and prove
`ss_tapeBlocks_zeroLeft`, `ss_prefix_return_fields`, and `ss_capturedPrefix_fields`. The latter
normalizes the returning capture without dependent rewriting beneath its embedding.

The following 15 private declarations completed phase 3:

| Declaration | Role |
| --- | --- |
| `ss_serialized_layout` | Specializes the public seam-layout contract to a canonical serialization, choosing time before any suffix/configuration. |
| `ss_bufferLeaf` | One-step conditional move of one work head, implemented by the public tape action. |
| `ss_bufferLeaf_run` | Silent framed step and first-return cut for that leaf. |
| `ss_bufferSkip_run` | First catalog skip from virtual position minus one, including the left blank. |
| `ss_bufferAdvance` | Public seam joining the conditional left step to a second catalog skip. |
| `ss_bufferAdvance_run` | Positions a nonempty word one cell beyond its right blank; handles the empty word separately. |
| `ss_bufferSeek` | Public seam joining the first skip and advance. |
| `ss_bufferSeek_run` | Exact framed forward-positioning contract and first return. |
| `ss_bufferBack_run` | Specializes catalog skip-back to that endpoint. |
| `ss_bufferClear` | Public seam joining a fixed empty-origin correction and catalog clear. |
| `ss_bufferClear_run` | Full erasure, head zero, and first return. |
| `ss_bufferFinish` | Public seam joining skip-back and the proved clear. |
| `ss_bufferFinish_run` | Framed backward-and-clear contract. |
| `ss_bufferCleanup` | Public seam joining the two positioning/cleanup halves. |
| `ss_bufferCleanup_run` | Uniform full buffer cleanup from every allowed initial head. |

No helper was removed. The partial Implementation status paragraph is now removed. The source has **1753 lines,
12 public / 39 private declarations**. All public statements and the other public bodies are unchanged; the
owned-region comparison is byte-equal outside the authorized regions. No line exceeds 100
characters. There is no new host, seam implementation, parser, embedding or layout machine.
All joins invoke the existing R2 constructor and its framed run/first-return theorems. The
conditional buffer leaf is a single action, not a scan or replacement catalog row.

Phase 4 adds six private declarations:

| Declaration | Role |
| --- | --- |
| `ss_RewindState` | Four finite control states with a separate pre-exit anchor. |
| `ss_inputRewind` | Native input-only leaf built from `FinTM.controlAction`. |
| `ss_inputRewind_done` | Stationary final-anchor contract through the public run equations. |
| `ss_inputRewind_run` | Exact code-position time, fixed work heads, and first final exit, using the public scan and rewind-head contracts. |
| `ss_live_map` | Normalizes a live state map through the five public field equations. |
| `ss_block_updates` | One shared pointwise argument giving the two-update normal form for both captured tapes and heads. |

`exists_selfStartupTMK` now has a complete proof assembling the four phases with the public R2
seams. The other two stubs are unchanged. In total there are 24 new private declarations over
the base's 15. Earlier changes to the two sketches and capture theorem remain as described.

## Construction, times and tapes

Let `G = bufferedCompTM universalPrefixTM (ss_cleanCanonizer E.canonizer)`, `m = G.k`,
`K = m + 1`, and `n = K + (k + 2)`. The capture uses `ss_sourceSlot m k` and
`ss_captureTape m k`. The concrete physical layout is:

| Tape | Index and endpoint |
| --- | --- |
| Simulated work tapes | `0 … k - 1`, blank at head zero |
| Table | `k`, `bufferTape (tableBitsK (E.machine α).tr)` at head zero |
| Summary | `k + 1`, unary initial state shifted by two, at head zero |
| Code buffer | `k + 2`, cleared and restored to head zero |
| Remaining cleaned source block | `k + 3 … k + 1 + m`, blank at head zero |
| Capture | `k + 2 + m`, cleared and restored to head zero |

Capture supplies functions `t α` and `p α` before the suffix, with `p α ≤ α.length + 1`.
The one fixed empty-code parameter is `p [] ≤ 1`. The machine is fixed before `α` and `w`.
The normalized capture ends with the code-buffer head at `p α - 1`, capture head at the
serialization length, native input position `2 * α.length + 3`, and empty physical output.

Let `v = if p α = 0 then [] else α.drop (p α - 1)` and
`w₀ = if p α = 0 then α else []`. For each code, choose the layout's `l` before its ambient
configuration; its bound is `l ≤ C * ((serializeK (E.machine α)).length + 1)`.

| Phase | Exact time |
| --- | --- |
| Returning capture | `a = 3 * α.length + 4 + t α` |
| Serialization redistribution | `l`, from the public contract |
| First skip | `v.length + 1` |
| Conditional left step and second skip | `w₀.length + 3` |
| Forward positioning, including its seam | `v.length + w₀.length + 5` |
| Backward skip | `α.length + 3` |
| Empty-origin correction and clear | `2 * α.length + 4` |
| Full cleanup, including internal seams | `b = v.length + w₀.length + 3 * α.length + 14` |
| Native input rewind and fresh final exit | `r = 2 * α.length + 5` |
| Whole startup, including three outer dispatches | `T = a + 1 + (l + 1 + (b + 1 + r))` |

Choose **`B = n * (T + 1)`** using `MultiTapeTM.spaceUsed_le_mul_succ`. Every time and the space
bound is chosen before `w`. No regularity assumption is made on `E.canonizerTime`.
The final output is empty, and the public append-only output-prefix theorem proves silence at
every earlier time. R2's inherited first-return cuts prove absence of the final exit before `T`.

At buffer head −1, the first skip crosses the left blank. At a nonnegative head it crosses the
remaining suffix. A conditional left step between two catalog skips handles both cases. The
backward catalog row then restores the first cell. For an empty code, its one fixed virtual
position is zero or one; the final conditional step restores its origin before clearing. This
does not assume a uniform origin for two indistinguishable all-blank configurations. All
contracts preserve arbitrary ambient tape contents, heads, input position and accumulated
output as appropriate. The index proof is valid for `k = 0`; `G.k > 0` follows from the public
buffered tape-count equation, including a zero-work-tape canonizer. Empty code and empty suffix
are covered without exclusions.

## Verification and governance

- Fresh bootstrap: all 95 supplied modules passed; 33 base sorry warnings in 14 modules;
  maximum RSS 2,927,084 KiB.
- Final sweep: **all 95 modules passed, zero errors, 32 sorry warnings in 14 modules;
  maximum RSS 2,939,516 KiB, summed module wall time 520.325 seconds**. The owned module has exactly the other two stubs' warnings. Every
  other module has exactly its base warning set. No owned admission remains.
- Full-file final seal: all **32 external definitions** in `seal-final.txt` locally
  irreducible, exit 0. Its only sorry warnings are the other two public targets. The inherited
  negative control fails as expected. The seal caught serialization rewrite order and three
  final state-map field closures; the checked final proof uses explicit published equations
  for all of them. No external definition is explicitly unfolded in a rewrite/simplification.
- Axiom prints: all **39 private declarations and three public targets**, inspected in
  `phase4-final-check3.log`. The only private helper with `sorryAx` is `ss_serialized_layout`,
  whose only admitted dependency is the permitted seam-layout theorem. The completed startup
  target has `[propext, sorryAx, Classical.choice, Quot.sound]` through that same dependency.
  Every other new helper is admission-free; the other two targets retain their own old sorries.
- Import probe: **all 121 names resolve, zero errors, exit 0**. The supplied 111 names are retained and ten public equations or
  framed contracts used by this proof are additionally checked.
- Owned-region and statement freeze: pass. No new public declaration; every private name starts
  `ss_`. Every nontrivial new proof has a literal Proof sketch. No added line exceeds 100.
- Manual inspection of every `rw`/`simp`/`simpa`/`change` argument: only local or owned
  definitions are reduced, and foreign TCSlib objects are read through their published APIs.
  No other-file private, post-base declaration or canonical R3 row is cited. See the rule 10
  and rule 11 records for the exact API families.
- Lint: **0 FAIL, 64 WARN over 82 files**. The sole additional warning is the file's size. The
  brief explicitly imposes no cap and forbids a cross-file split, so the private contracts stay
  beside their consumer. This decision is recorded. No host, seam, parser, embedding or layout
  implementation is duplicated: composition uses R2 throughout; scanning and erasure use the
  named catalog rows; native rewind uses the published scan and rewind-head theorems.
- Before screen: **674 declarations, 514 pairs, 151,065 characters** (identical to the supplied
  base). Final after screen: **696 declarations, 525 pairs, 162,136 characters**. Both final outputs and the pair diff are included.
- All eleven new pairs are within UniversalK and below 90%: captured fields/run (56%); seek/
  finish (84%, 69%); cleanup/finish (81%, 56%); cleanup/seek (80%, 67%); advance/clear (50%);
  cleanup/live-map (51%); finish/live-map (51%); rewind-run/rewind-done (55%). They share framed
  statements and applications of the same public seams/field equations. The rewind run invokes
  the single stationary-done lemma; it does not repeat that induction. No new cross-file pair.
  **new copies: none**.

Escalations: **none**. Required promotion candidates: **none**. The one-step conditional work
head move and live-map field adapter could be promoted if another consumer appears; they are
private here and require no upstream API change. No owned proof remains open. The existing
`exists_selfUniversalK` and `universalK` are outside scope and unchanged.

Checkpoint 3 packaging correction: its inherited closing sentence says “two format-patch
commits”; that archive actually contains three, as its patch directory and manifest show.
The final archive contains all four commits against the shared base.

## Shared environment

- Initial preflight: 9 CPUs; disk free 23,909,351,424 bytes (22.2673 GiB), filesystem overlay.
- Memory limit 8,589,934,592 bytes; `anon + kernel + shmem = 294,219,776` bytes;
  headroom `8,295,714,816` bytes (7.7260 GiB). `oom = oom_kill = 0`.
  Page cache was excluded exactly as the addendum requires.
- Disk before cache, after toolchain: 19,655,630,848 bytes, above the 8 GiB floor.
- Lean 4.25.0. Unmodified Lean failed with `error: failed to locate application`.
  The authorized exact shim SHA-256 is
  `985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
  The source is included; the compiled shared object is excluded.
- Lean/Lake wrappers set `LEAN_SYSROOT` and `LAKE_HOME` to
  `/workspace/scratch/f441fd79989b/lean-4.25.0-linux`, and `LD_PRELOAD` to
  `/workspace/scratch/f441fd79989b/executable-path.so`. These settings are scoped to the
  Lean/Lake invocations. `TMPDIR` is the disk-backed clone's `evidence/tmp`.
- Shared cache: 40 Mathlib roots, 95 modules in the union; `TAR_OPTIONS=--no-same-owner`.
  The narrowed command exited 0, downloaded 35 missing files, and unpacked 1,002 files;
  no download failed. No retry was needed. Every present package URL and commit matched the
  manifest; optional doc-generation packages were not enabled. Zero empty oleans; Mathlib-root
  probe passed. No package tree was copied or moved, and no unfiltered cache command or project
  `lake build` was run.
- One Lean check at a time and one screen at a time. `/usr/bin/time` is unavailable, so the
  sequential runner records each command's start/end and `os.wait4` maximum RSS instead.

The ZIP contains REPORT.md, the full modified source, four format-patch commits, a git bundle
whose sole prerequisite is the shared base, bootstrap/final/axiom/probe/seal/lint/screen logs,
source evidence and SHA256SUMS. Build products and the compiled shim are excluded. Bundle
verification and ZIP CRC/manifest verification pass. Nothing was pushed or merged.

Final sweep tail:

```text
  simp_all ̵[̵V̵i̵r̵t̵u̵a̵l̵T̵a̵g̵]̵

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
END 94/95 TCSlib/Complexity/TuringMachine/Universal 2026-10-22T06:13:48.266538+00:00 EXIT 0 WALL_SECONDS 13.417 MAX_RSS_KIB 2176960
START 95/95 TCSlib/Complexity/TuringMachine 2026-10-22T06:13:48.266590+00:00
END 95/95 TCSlib/Complexity/TuringMachine 2026-10-22T06:13:49.553041+00:00 EXIT 0 WALL_SECONDS 1.287 MAX_RSS_KIB 2047804
```
