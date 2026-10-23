# External audit pack — U2-S continuation 1: the `k`-generic startup (PR #147, a fill gate)

Campaign: the Arora-Barak chapters 1 and 4 work on the universal machine (U2, the `k`-tape
universal machine; [AB09, §1.4, Theorem 1.9], and the space-universal machine of §4.1.3). The
fill brief U2-S (`campaign/fills/u2s/briefs/u2s-fill-startup.md`) targets
`Turing.exists_selfStartupTMK` (`TCSlib/Complexity/TuringMachine/UniversalK.lean`): the
`k`-generic startup, which captures the input's code, lays it out on the step block's tapes and
returns to the seam. Its first round landed 15 private helpers as a partial (#130, gate 48).
**Continuation 1** (`campaign/fills/u2s/briefs/u2s-fill-startup-cont1.md`), item 1 of megafill B
(`campaign/fills/megafill/briefs/megafill-B.md`), was delivered complete on 2026-10-22: the target
is proved, modulo only `Turing.exists_seamLayoutTM`, which #145 proved and which has merged. The
worker's report is `campaign/fills/u2s/reports/startup-cont1-REPORT.md`; the maintainer's review,
`campaign/fills/u2s/reviews/startup-cont1/REVIEW.md` ("complete; land after #145").

**The head:** `lean/u2s-startup-cont1` at `28150fc1`; its merge-base with the campaign branch is
`144201de` (after #145, #146 and #148). This bundle's records are from the campaign branch's
later records commit (stated in the bundle's README).
- `89332143`, `14b1ac5c`, `90bf1840`, `7e9aff5b`: the worker's four commits (`51a8c643..8e1aee0f`,
  on the base `6cfee544`), cherry-picked from the verified bundle; they touch only the owned file
  (the first adds the authorized `Build/SeamLayout` import);
- `c6733db3`, the maintainer's, docstrings only: the module's status and main results, and the
  `TuringMachine` facade's line;
- `28150fc1`: the campaign branch merged in after #145, #146 and #148 (the facade auto-merged;
  `UniversalK` unchanged by the merge).

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target proved** | `Turing.exists_selfStartupTMK` (the `k`-generic startup; its `k = 1` corollary `SelfUniversal`'s `Turing.exists_selfStartupTM` with it) |
| **Privates added** (24, `ss_`) | the capture over the buffered composite and its fields (`ss_capturedPrefix_fields`, `ss_prefix_return_fields`, `ss_live_map`, `ss_block_updates`, `ss_tapeBlocks_zeroLeft`); the redistribution by the seam layout (`ss_serialized_layout`); the code buffer's cleanup (`ss_bufferSeek`, `ss_bufferSkip_run`, `ss_bufferLeaf`, `ss_bufferAdvance`, `ss_bufferBack_run`, `ss_bufferFinish`, `ss_bufferClear`, `ss_bufferCleanup` and their run lemmas); the native input's rewind (`ss_RewindState`, `ss_inputRewind` and its lemmas) |
| **Privates changed** (3) | `ss_captureInitial`, `ss_capture_indices`, `ss_capturedPrefix_run` (restated over the buffered composite) |
| **Frozen** | every public statement and docstring of the base, the target's included (12 → 12 public declarations, at source) |
| **Size** | 1,753 lines; 12 public, 15 → 39 private (`evidence/land/landing-checks.txt`) |

## Brief for the auditor

1. **Faithfulness.** Does the proof establish the frozen statement for every effective code `E`
   and every input, with `T = a + 1 + (l + 1 + (b + 1 + r))` and `B = n·(T + 1)` chosen from the
   code alone, before `w`? At the boundaries in particular: the empty code (`α = []`), a code
   whose buffer is a single cell, the empty input word, and `k = 1`.
2. **The accepted refinement (the review's F1, the user's ruling of 2026-10-22).** The code
   buffer's cleanup uses a second private one-step leaf (`ss_bufferLeaf`, one `tapeAction` that
   moves the tested head only on a blank cell) beyond the brief's one allowed leaf, and the
   canonizer's final virtual input position on the empty code, `p [] ≤ 1`, as a fixed parameter of
   `E`, because on the empty code the buffer is all blank and no machine can locate its head at
   `−1` against `0`. Is the leaf correct, read only through public step lemmas, and is the
   dependence on `E` allowed by the statement (`∀ E, ∃ R …`)?
3. **The route.** The capture over the composite (through the cast pair of #132), its
   normalization through the public field equations, `exists_seamLayoutTM` with `src` the capture
   tape, the catalog skip, skip-back and clear, the native input's rewind, and R2 seams only (no
   new host, seam, loop or embedding). Does every seam's cut and frame hold as used?
4. **Admission.** On the merged tree, the target, its `k = 1` corollary and the seam layout each
   depend on exactly `[propext, Classical.choice, Quot.sound]`
   (`evidence/land/axioms-merged-lu2sc1.out`, against the replay's snapshot). Before #145, the
   review found `sorryAx` reaching the target only through `exists_seamLayoutTM`.
5. **Rule 10.** The review sealed 32 other-file definitions, erased three simp sets, and recorded
   36 controls that fail sealed and pass unsealed; no other-file definition is passed to `rw`,
   `simp` or `dsimp`, and there is no `unfold` (`reviews/startup-cont1/out/`). Does any step still
   close only because another file's definition reduces? Rule 11 (no R3 row, no other file's
   private).
6. **Duplication.** The v3 screen: 674 → 696 declarations, 514 → 525 pairs; 11 new pairs, all
   in-file, at most 84%. The brief's known hazards are the chapter-1 startup
   (`universalCanonTM`, `universalCaptureTM`) and UN's and R's header captures: is anything
   transcribed from them?
7. **The text.** The module's status and main results, and the facade's line (`c6733db3`): accurate
   and public-facing (no campaign labels, paths or dates in new Lean text)?

## Repository-side attestations (verify or challenge)

- **Elaboration** (the review): 0 errors at the base and at the tip, with only the other two
  stubs' sorry warnings (`exists_selfUniversalK`, `universalK`). The replay below elaborates the
  merged head: `UniversalK` 0 errors, the same two sorry warnings.
- **Code identity** (the maintainer, at `28150fc1`): `UniversalK` equals the worker's head
  `8e1aee0f` with comments stripped; the freeze from the base `6cfee544`: 12 → 12 public, 15 → 39
  private, the only public body change the target's (`evidence/land/landing-checks.txt`).
- **Axioms** (the review): 43 prints, equal print for print to the worker's 42. On the merged tree:
  item 4 above.
- **Probes** (the review): the brief's 111 checks, and the worker's 121 checks of 118 names, 0
  errors.
- **Lint** (the merged head): `TuringMachine` 0 FAIL, 67 WARN over 82 files; `UniversalK`'s two
  warnings are its size and two public definitions without a lemma beside them (both from the
  base) (`evidence/land/lint-tm.txt`).
- **The sweep** (the worker): 95 modules, 0 errors; sorry warnings 33 → 32, every other module
  unchanged by name.
- **Environment:** megafill B, under addendum v2.4.
- **Replay:** `replay-lu2sc1.sh`: the downstream closure, on the merged tree `28150fc1`, of every
  file changed since #144's merge (6 modules: `Build/InputDevice`, `Build/SeamLayout`,
  `Build/ZoneRebalance`, `UniversalK`, `SelfUniversal`, the facade last), chained from
  `oleans-lsk2` (the tree of `0416ffea`). **Passed (user, 2026-10-22):** 6 of 6, 0 failed,
  static-equal (4) (`evidence/replay-lu2sc1.*`).
- **Merge order:** #149 (the space API) replays a closure containing this one's; it merges first,
  and this PR then re-replays its six modules on the merged tree.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/63-u2s-startup-cont1-fill/findings.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `u2s-startup-cont1-fill-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
