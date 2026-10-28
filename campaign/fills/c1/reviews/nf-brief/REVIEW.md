# Review: the NF fill brief draft (`c1-fill-nf.DRAFT.md`, `Turing.FinNDTM.exists_codeNDTM_accepts_linear`)

**Verdict: issue after the listed edits.** No redesign is needed. The route is sound against #174's
exact statements. Composed with the packaging and the trivial setup, the host's two acceptance
lemmas give the target from three obligations on `V`. I proved that composition sealed
(`rv_skeleton`, section (d)).

The draft has **2 majors**, both about published rows:
- **F1.** Sweep 0 is the published scan fold `Turing.scanTM`, so it is not an own leaf.
- **F2.** A's rewind and B's clear do not fit the rows the draft names, as the draft describes
  them. Each has a published fix inside the imports.

It also has **11 minors** and **7 notes**. Every line number, blob, count and path I checked is
right, except region (d)'s "20–21", which should be 20–22 (F3). Every input exists as named. The
pre-ship's Lean outputs reproduce byte for byte.

Read-only review by the maintainer's review sub-agent, 2026-10-27.
- **Inputs.** The draft is SHA-256 `783c6ab1…bec8a68` (`orig/`), unchanged from `7a726612` to the
  records tip `55b711c0`. The inputs are `campaign/fills/c1/inputs/c1-fill-nf/`, unchanged over the
  same range.
- **Tree.** `wt/`, detached at `c2887fb5` (#174's merge), with the `.lake/packages` link.
  `c2887fb5`'s TCSlib equals `086c0ef0`'s and the records tip's (out/00-trees.txt). The owned blob
  is `5150734a89b935396dee9516911030497f2034d1`, 88 lines.
- **Lean.** Only through `tools/leanelab.sh` (`scripts/elab.sh`), one elaboration at a time,
  against `oleans-lnfapi4`. There was no build, no cache command and no copy-text screen.
- **Probes and Python.** Probe files were written in `wt/rvprobe/` only and are kept here as
  `probe/*.lean.txt`. Python ran with `python3 -I`, from scripts in `scripts/`.
- **No changes.** `wt-hk` and the main checkout were not modified, and nothing was pushed. To grep
  the two open PR heads (#175, #176), I fetched them into the review worktree's own `FETCH_HEAD`.
  No ref changed.
- **Evidence.** Every claim cites `out/`. `out/01-review-runs.txt` tabulates every elaboration.

## (a) Accuracy

| Claim (draft line) | Result | Evidence |
|---|---|---|
| Blob `5150734a…` (51); 88 lines, 1 public, 0 private (72–73, 282) | right | out/00-trees.txt |
| NDNormalForm 6–7 imports, 43 `namespace FinNDTM`, 45–77 docstring, 46 status phrase, 66 "(round-1 finding 6)", 78 target, 84 `sorry` (134–147) | right | out/02-cited-lines.txt |
| 20–21 "the sentence on where the statement lived" (139) | **the sentence ends on line 22** ("…so / that its fill can run beside…"), which is also campaign text (F3) | out/02-cited-lines.txt |
| 30–31 "(sorried; phase P3.3)" (140) | right | out/02 |
| NDHost 571 `CtlState`; the five lemmas from 1707 (114–115) | right: 1707 opens the handoff lemma's docstring, and the theorems are at 1721, 1760, 1809, 1951, 1999 | out/02 |
| NTIME 96, NDCodes 99 (101–102) | right (`def AcceptsWithin`, `structure CodeNDTM`) | out/02 |
| StepBlock 136–198 (117) | right (the section header is at 136, and `summaryEmit_none` is at 198–199) | out/02 |
| 19 case lemmas (21) | right (6 `ctlState_*`, 6 `guessCtlRunPhases_*`, 7 `guessCtlRunRed_*`) | NDHost 604–772 |
| Import probe 88 of 88, 0 errors (122) | right, identical to the pre-ship | out/00-preship-compare.txt, out/NFImportProbe.out |
| Route probe: 9 sealed, 4 erased, standard axioms or fewer; 9 controls (123–125) | right: `nfr_pack` uses the standard three, `nfr_setup` uses `propext` and `Quot.sound`; 9 errors at lines 57–91, all in the sealed section | out/NFRouteProbe.out, out/NFRouteSealControl.out |
| Order list: 112 modules, 39 Mathlib roots (126) | right. The list equals the closure of NDNormalForm's downstream (the two facades and `NTimeHierarchy`), and it is topological. The 40th direct import is `Std.Sat.CNF`, which is not Mathlib | out/03-order-check.txt |
| 20 base sorries in 9 modules (126, 445) | right; my textual census agrees module by module | out/04-sorry-census.txt |
| Screen base 1,344 / 862 / 274,615; 763.8 s, 3.17 GB (127, 390–392) | the log says so; not re-run (excluded) | logs/c1-fill-nf-screen-base.txt |
| Lint: ClassNP 0 FAIL, 16 WARN over 21 files; policy linter 0 on the file (129) | right, identical | out/lint-ClassNP.txt, out/style_lint-NDNormalForm.txt |
| Overlay: one warning, the target's sorry (77–78, 121) | right (overlay line 80) | out/NDNormalFormOverlay.out |
| Every path named (gates ch3-p33, 38, 85; the design note; standards; scripts; logs; order list; inputs) | all exist; gate 38's records name PR #120 | out/08-paths.txt |
| `nf_`/`Nf` unused in the tree and on #175/#176 (338–339) | right | out/05-prefix-grep.txt |
| In flight (80–84) | #175 touches only `SpaceComplexity/{Constructible,Savitch}`, outside the list. E-Q cont1's landing is now **#176**, and `NTimeDiagonalizer` is an *import* of the downstream `NTimeHierarchy`, not downstream itself. **#177** (opened 2026-10-28 06:04Z, after the draft) changes `ClassNP/Reductions`, which is in the order list (45) as an import of the `ClassNP` facade, and is missing (F17) | out/09-open-prs.txt, out/03 |
| Only `NTimeHierarchy` cites the target (83) | right; the two facades only import it | NTimeHierarchy:1825 |

## (b) The route against the host's exact statements

**Sound and complete at the interface.** I proved `rv_skeleton` sealed over 39 definitions: the
draft's 29 and 10 more (out/NFReviewProbe.out, standard three). For any
`V : MultiTapeTM 2 Bool SQ` with `[Fintype SQ] [DecidableEq SQ]` and any finite controller, the
target's statement follows from three hypotheses:
- `hfwd`: per accepting `N`-run, a first-stopping `s` with `hacc`, `hfirst` (neither verdict
  before `TQ`) and `hnil`, and the budget `0 + 2 * s.length + TQ + 11 ≤ C * (t + 1)`. The budget
  is syntactically the forward lemma's `hB` at `TP = 0`.
- `hV`: per input `x`, exactly the backward lemma's `hV` at `cP := P.initCfg x`.
- `hbwd`: a first-stopping `s` on which `V` first reaches `acc` with output `[]` gives
  `∃ t', N.AcceptsWithin x t'`.

The proof is `nfr_pack` on `guessCtlRunTM rvP rvP.q₀ 0 q₀ δ stop false V qentry acc rej`, then
`nfr_setup` and one application of each acceptance lemma.

On the questions the brief was checked against:
- **Fintype of the host's states.** The Sigma state type gets its `Fintype` by
  `instFintypeCtlState` through instance resolution (out/RVShapes.out).
- **`DecidableEq` is not needed for the packaging.** `Fintype.equivFin` takes only `Fintype`.
  `DecidableEq` is needed for `SQ` and `SP` by `guessCtlRunTM` (F18).
- **The display, `Q := Fin W × Bool`, and the stop at a record boundary after a flagged record.**
  These match `hslive`/`hsstop` (`∀ i < |s|, stop ((s.take i).foldl δ q₀) = false`,
  `stop (s.foldl δ q₀) = true`).
- **"A stopped stream is complete records, the last and only the last flagged."** This is right
  *for* `q₀ = (0, false)`, `δ (p, f) b = if p = W − 1 then (0, b) else (p + 1, f)` and
  `stop (p, f) = (p = 0 ∧ f)`, with the flag as the record's last bit, which is the layout of
  line 179. The reasoning:
  - After `i` bits the position is `i mod W`, and the flag is that of the last complete record
    (or `false` before the first).
  - So the first stop is the first boundary after a flagged record, which gives `n ≥ 1` complete
    records with only the last flagged.
  - With an initial flag `true` the empty stream would stop.

  The draft never pins `q₀`, `δ` or `stop`. The converse (stopped ⇒ records) is needed by `hV`
  and the backward transfer, and no checkpoint names it (F9).
- **`guessRunCfg`'s layout as `V`'s start.** It is exactly `streamStartCfg x 0 qentry s` (input
  head `1`, `s` on A from `0` and blank elsewhere, B blank, heads `0`, output `[]`). I proved this
  sealed from the field equations as `rv_entry`. `guessRunCfg_clean` does not apply here, since it
  needs a capture tape outside the selection.
- **`hV` is stated exactly as the backward lemma needs it** (draft 211–215: "every stream that
  first stops the controller at its end … reaches `acc` or `rej` … and is at neither before").
  `rv_skeleton` passes `hV x` to `guessCtlRunTM_stream_of_accepts` unchanged.
- **Nothing is forgotten.**
  - The gate-guidance bullet (250) names `hfirst` and `hnil`.
  - The forward bullet (218–222) says only "V accepts it with an empty output". It should name
    `hacc`/`hfirst` ("at neither verdict before")/`hnil` (F12).
  - Silence of `V` (174) is right: phase-host redirects are silent (`phaseHostTM_tr_of_red_some`).
- **`t₀ ≥ 1`** holds since `N.initCfg` is live, so `N.AcceptsWithin x 0` is false.
  **AcceptsWithin's exact length** is absorbed by the forward lemma (any `B ≥` bound) and by
  `nfr_pack`.

## (c) Mathematical gaps, and rule 10

No mathematical gap, and no rule-10 gap. Every reading a route step needs is published inside the
overlay's 26-module closure (out/overlay-import-closure.txt), and the 61 names below elaborate
with 0 errors (out/NFReviewImportProbe.out).
- **`NDTM.tr`'s argument order** is `tr (choice) (q) (input) (work)` (Nondeterministic:127), so
  `aᵣ := N.tm.tr bᵣ qᵣ ιᵣ ωᵣ`, with the claimed input read `ιᵣ` and the work reads
  `ωᵣ : Fin N.k → Option Bool`. "`N.tm.tr bᵣ qᵣ σᵣ`" (181) is shorthand for that. N's step reads
  through **`NDTM.stepWith_of_some`/`_of_halt`**, which the draft never names: it names only
  `MultiTapeTM.step_of_some` (F5).
- **The claimed reads.** `Option Bool` has 3 values in a 2-bit block, so the fourth code needs a
  total meaning (F19).
- **B's replay.**
  - Work tapes are `ℤ → Option Bool`, and a write is `Option (Option Bool)`. `some none` erases,
    and an outer `none` keeps the scanned symbol (`Action.apply_workTapes`, `Simulation:89`,
    inside the closure).
  - A head moves by `+ ↑(SignType)` (`Action.apply_workTapePos`), so B moves `2d`.
  - Every visited block is written nonblank on *every* stream, so the visited region is a
    contiguous delimited word. That is what lets the published clear apply (F2).
- **The input sweep.**
  - The input head is clamped in `Fin (|x| + 2)`, and N and V move it by the same `moveInputPos`
    (`Action.apply_inputPos`), so their positions agree.
  - Transferring a checked claim needs "same input position ⇒ same `inputSymbol`" across machines
    with different tapes and states. I proved it sealed from `Cfg.inputSymbol_of_zero`, `_of_end`
    and `inputSymbolInner` as `rv_inputSymbol_congr`. It exists only as two **privates**,
    `ExhaustiveReplay`'s `xr_inputSymbol_congr` (line 200, same statement) and `ZoneRebalance`'s
    `zr_inputSymbol_congr`, which is a known hazard to name (F10).
  - `inputRewindTM`'s `p ≥ 1` (InputRewind:96) is real. But the return is unnecessary (F4), and so
    is the head bound `rv_moveInputPos_le` that it would need.
- **The output summary.** `outputSummary_append` (`w ++ b.toList`) matches `Action.apply_output`
  (`c.output ++ a.output.toList`). Then `outputSummary_nil` and `outputSummary_true` give "exactly
  `[true]`". The draft is right. Note that `summaryEmit s none = s` is not `rfl` for a variable
  `s`, since it is matched on both arguments (out/NFReviewSealControl.v1.out), so use the laws.
- **The backward induction** is right as stated (225–228). If the reads before `r` are genuine, the
  recomputed actions are N's, so the replayed input position and tapes are N's at `r`, and the
  passing sweeps make `σᵣ` genuine. The control check forces "not flagged ⇒ live" on every
  non-last record, so N halts exactly at the record count with output `[true]`.
- **`N.k = 0`.** Then `W = 4`, there are no tape sweeps, and the phase index over `Fin N.k` is
  empty. Right.
- **`FinNDTM`'s fields** are projections of a variable, so nothing is unfolded. Its instances are
  `fintypeState`/`decEqState`.

## (d) Probes

**The pre-ship, re-run:** route probe, seal controls, import probe and overlay are byte-identical
(out/00-preship-compare.txt). I scanned them first: they contain only imports, `open`,
`section`/`end`, attributes, theorems, examples, `#check` and `#print axioms`.

**The review's own probes** (`probe/`; out/01-review-runs.txt):

| Probe | What it shows | Result |
|---|---|---|
| `NFReviewProbe` (sealed over 39: the route probe's 9, the draft's 20, and `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `streamStartCfg`, `scanTM`, `scanResult`, `scanFold`, `scanKeep`, `clearTM`, `FinTM.controlAction`, `tapeAction`) | `rv_pack`/`rv_setup` (the route probe's); **`rv_skeleton`** (b); **`rv_entry`**; **`rv_sweep0`**: from the entry, `scanTM 2 0 (scanFold δ) scanKeep a₀` is at `done (s.foldl δ a₀)` at exactly `2|s| + 2`, no `done` before, and every field is the entry's (A's head back at `0`); `rv_inputSymbol_congr`; `rv_moveInputPos_le` | exit 0; 7 prints, all within the standard three (out/NFReviewProbe.out) |
| `NFReviewSealControl` | 30 controls for the 30 definitions beyond the 9 | **all 30 close unsealed; all 30 fail sealed.** Two (`guessCtlRunPhases`, `guessCtlRunRed`) fail at *elaboration*, because `CtlState` is sealed. With only the three host definitions sealed, all three fail at their `rfl` (out/NFReviewSealControl.summary.txt). The draft's 20 names all exist (the seal accepts them) |
| `NFReviewVProbe` | a one-sweep `V` in the route's shape, `phaseHostTM` over {scan fold, verdict park}: its first verdict `pass (s.foldl δ a₀)` at exactly `2|s| + 3`, neither verdict before, output `[]` (that is, `hacc`/`hfirst`/`hnil`, and `hV`'s shape) | exit 0; standard three (out/NFReviewVProbe.out) |
| `NFReviewImportProbe` | 61 names the route needs that the 88 omit | 0 errors (out/NFReviewImportProbe.out) |
| `NFReviewDupProbe` (+ `Raw`) | `exact?` on `rv_entry`, `rv_sweep0`, `rv_inputSymbol_congr`, `rv_moveInputPos_le` | 4 of 4 "could not close" (out/NFReviewDupProbeRaw.out); grep finds the two privates of F10 and no public form (out/07-dup-search.txt) |
| `RVUnfoldUnderSeal` | an explicit `unfold MultiTapeTM.step`/`simp only [Action.apply]` passes the seal; only the `rfl` closure fails | 1 error, the `rfl` (out/RVUnfoldUnderSeal.out), F15 |

## (e) Brief hygiene

- **Regions (a)–(d)** are consistent with the file, except that 20–21 should be 20–22 (F3).
  Region (b)'s placement matches the precedent.
- **Ground rules** match E-Q cont1's and addendum v2.6: Part 3 items 5 and 7, the cache rule, and
  "a process deviation never ends the item". Three issues:
  - rule 7 omits the rows F1/F2 make binding;
  - rule 11's `nf_` prefix contradicts "copy `nfr_pack`/`nfr_setup` as privates" (F8);
  - the docstring, proof-sketch and public-facing rules for *new* declarations, which the
    precedent carries in region (d), are missing (F7).
- **The seal list.**
  - Every listed name exists.
  - It omits `Cfg.inputSymbol` and `Cfg.workTapeSymbols`, which are in every
    `step_of_some`/`stepWith_of_some` reading, and the rows F1/F2 add (F6).
  - Sealing `GuessRunPhase.CtlState` blocks writing any host state. The route needs none, but the
    brief should say so (F14).
  - Sealing `step` and `Action.apply` is compatible with the own-leaf allowance only for explicit
    unfolding (F15).
- **The screen population** labels `Build/Contract/{Catalog,Basic}` "files the route cites", but
  neither is in the overlay's closure. It misses the `ChoiceReplay` hazard (F11).
- **The checkpoints** follow from the route. With F1, F2, F4 and F9, checkpoints 1–4 change.
- **The REPORT checklist** is consistent. Add the leaf docstring line (F7).
- **Leftovers from E-Q cont1.** The pitfall "the stream after the setup's `TP + 1` bits" (506–507)
  is internal to the host and never meets the fill (F16). The rest is NF-specific.

## (f) Sizes, risk, and pre-ship additions

- **Size.** 2.2–4.5k is realistic. F1 and F2 remove sweep 0's machine and B's and A's private
  returns, so expect the lower half. My split:
  - layout and controller (both directions): 0.3–0.5k;
  - sweep 0's fold and its laws: 0.2–0.4k;
  - the replay leaf and its run lemma: 0.8–1.5k;
  - `V`'s composition over a `Fin N.k`-indexed phase chain and its first-verdict
    characterization: 0.4–0.8k;
  - forward with the ledger: 0.3–0.6k;
  - backward: 0.3–0.6k;
  - packaging: 0.1k.
- **The riskiest step** is the replay leaf's run lemma on B. It has two heads, the 2-cell block
  protocol at `ℤ` positions (read, compare, write via `Function.update`, move `2d`), rejection at
  the first mismatch, and it serves the forward exact-time run, `hV` and the backward genuineness.
  Second is `V`'s composition: an induction over `j < N.k`, one `phaseHostTM_run` per phase, with
  the redirect chain.
  - **Recommended shape.** State each leaf's run lemma as "after `r` records the configuration is
    a pure fold of the stream", as `scanTM_run_ofCfg` does with `scanResult`.
  - Then state `V`'s lemma as a characterization: "on every stopped stream, the first verdict is
    at `T(s)`, and it is `acc` iff every fold passes". That one lemma gives `hV`, the forward
    `hacc`/`hfirst` and the backward "acc ⇒ all passed".
  - The transfers then reason about folds only (F13).
- **Before issue, add to the inputs:**
  1. `NFReviewProbe`'s `rv_skeleton`, `rv_entry`, `rv_sweep0` and `rv_inputSymbol_congr` (as
     `nfr_` probe lemmas the fill may copy as `nf_`), with `NFReviewSealControl`'s 30 controls;
  2. the import probe extended by `NFReviewImportProbe`'s 61 names (149 checks);
  3. optionally, a k-phase version of `NFReviewVProbe`: phases indexed by `Option (Fin k)` with an
     abstract leaf run hypothesis, composed by induction on `j`. It would retire the second risk
     before the fill.

  None needs a prerequisite PR.

## Findings

| # | Severity | Where (draft line) | Finding | Evidence | Fix |
|---|---|---|---|---|---|
| F1 | major | 167–170, 189–193, 205–209, 349 | **Sweep 0 is a published row.** The control check is a finite-state fold over A's bits, which is exactly `Turing.scanTM 2 0 (scanFold δ₀) scanKeep a₀`. With `scanTM_run_ofCfg` and `scanResult_fold`, from the entry it is at `done (s.foldl δ₀ a₀)` at exactly `2|s| + 2`, with no `done` before, the word intact, and A's head back at `0`, so no rewind is needed. The draft has the fill hand-write it as an own leaf "by induction over records through `step_of_some`". That breaks the host-first and construction-reuse rule (`policy.md` §1, checklist 8), and the precedent's "L4 is not a leaf" (E-Q cont1). `scanTM` is in `Build/Catalog`, inside the imports | out/NFReviewProbe.out (`rv_sweep0`), out/NFReviewVProbe.out, Catalog:12835–12880, 13147 | Replace item 1 of `V`'s phases and the "one leaf" paragraph (appendix A1). Hosts bullet: add `scanTM` (A1). Checkpoint 2 → "**Sweep 0:** the fold `δ₀` and its laws (its run is `scanTM_run_ofCfg` with `scanResult_fold`)." |
| F2 | major | 169, 189, 202, 213–215, 351 | **A's rewind and B's clear do not fit the named rows as described.** `skipBackTM_run_ofCfg` needs the word to end *one blank before the head*, that is, the head one cell past the blank. A sweep that "ends at the blank after `s`" leaves it on the blank, where the row does not apply. `Build/Rewind`'s `rewindTM`, which does apply, says so but is outside the overlay's imports. B's head ends inside the visited region, which no named row returns from, and rule 7 forbids a second rewind. Published fixes inside the imports: for A, `skipTM` (one step right on the blank, `w := []`) then `skipBackTM` (`u := s`), as the host does; for B, `skipTM` (over the region from the head), `skipBackTM` (`u :=` the region), then `clearTM` (`clearTM_run_ofCfg`), which ends blank with the head at the region's first cell | Catalog:12290–12316 (`skipBackTM_run_ofCfg`'s docstring and statement), 1505–1540 (`clearTM_run_ofCfg`); Rewind's docstring; out/overlay-import-closure.txt | Appendix A2 (sweep 3's last sentence, the A-return paragraph, `hV`'s sentence). Rule 7 → "Never write a second host, writer, phase composition, handoff, scan, clear, step right, rewind, input rewind or run decomposition." Checkpoint 4 → "… and B's clear (`skipTM`, `skipBackTM`, `clearTM` on B)." |
| F3 | minor | 139–140 | Region (d)'s "lines 20–21 (the sentence on where the statement lived)": the sentence continues to line 22 ("that its fill can run beside the universal machine's in `NTimeHierarchy`."), which also names a fill. Under rule 1 the fill could not touch 22 | out/02-cited-lines.txt | "the module docstring's lines 20–22 (the two sentences on where the statement lived and why it moved)" |
| F4 | minor | 27, 170, 196–197, 257, 318, 350 | The input head's return is unnecessary. No later phase reads the input (`scanTM`, `skipTM`, `skipBackTM`, `clearTM` and the tape mode ignore it), and the acceptance lemmas constrain only `V`'s state and output. It costs the `p ≥ 1` precondition and a clamped-position time bound | InputRewind:95–103; out/NFReviewProbe.out (`rv_skeleton`) | Replace "Then `inputRewindTM` returns … step right first)." with "The input head is not returned: no later phase reads the input, and the acceptance lemmas constrain only `V`'s state and output." Drop `inputRewindTM` from the Hosts bullet (170) and checkpoint 3's "and the input head's return". (Keep it in the import probe and the seal list: harmless.) |
| F5 | minor | 252–262, 208 | "all in `NFImportProbe.lean.txt`" is false. The draft cites `GuessRunPhase.instFintypeCtlState`/`instDecidableEqCtlState`, the `guessRunCfg_*` and `Cfg.mapState_*` field equations and `runFrom_zero`, none of which is among the 88. The route also needs names the draft never gives: `NDTM.stepWith_of_some`/`_of_halt` (N's step), `MultiTapeTM.step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, the input readings `Cfg.inputSymbol_of_zero`, `_of_end`, `inputSymbolInner`, `Cfg.workTapeSymbols_eq`, `moveInputPos_*`, `FinTM.bufferTape_*`, `streamStartCfg_*`, and the F1/F2 rows. All 61 elaborate | out/06-draft-names-vs-probe.txt, out/NFReviewImportProbe.out | Heading → "(public and proved at the issue commit; all in `NFImportProbe.lean.txt`, 149 checks)". Ship the probe extended by `probe/NFReviewImportProbe.lean.txt`'s 61. Add to the list: "N's step through `NDTM.stepWith_of_some` and `stepWith_of_halt`; the readings of the input head (`Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`, `inputSymbolInner`) and of the work heads (`Cfg.workTapeSymbols_eq`); `moveInputPos_*`; `FinTM.bufferTape_eq`, `_of_neg`, `_nat`, `_left`; the field equations of `guessRunCfg`, `streamStartCfg`, `Cfg.mapState`, `Action.mapState`; `scanTM`, `scanTM_run_ofCfg`, `scanFold`, `scanKeep`, `scanResult_fold`, `clearTM`, `clearTM_run_ofCfg`; the two `CtlState` instances." |
| F6 | minor | 313–321 | The seal list omits definitions the route's proofs mention: `Cfg.inputSymbol` and `Cfg.workTapeSymbols` (in every `step_of_some`/`stepWith_of_some` right-hand side) and, with F1/F2, `streamStartCfg`, `scanTM`, `scanResult`, `scanFold`, `scanKeep`, `clearTM`, plus any catalog action builder a leaf uses. With `CtlState` sealed, the controls of `guessCtlRunPhases` and `guessCtlRunRed` fail at elaboration, not at their `rfl` | out/NFReviewSealControl.summary.txt | After "`FinTM.bufferTape`, `moveInputPos`" add "`Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `streamStartCfg`, `scanTM`, `scanResult`, `scanFold`, `scanKeep`, `clearTM`, and any action builder your leaf uses (`FinTM.controlAction`, `tapeAction`, `inputMoveAction`)". After "(recursive definitions, as `NDTM.runWith`, get usage controls)" add "; with `GuessRunPhase.CtlState` sealed, a control whose statement needs `CtlState` to reduce (those of `guessCtlRunPhases`, `guessCtlRunRed`) fails at elaboration: run those two with `CtlState` unsealed too, where they must fail at their `rfl`". Ship the review's 30 controls |
| F7 | minor | 131–145 | The rules for *new* declarations are missing: a docstring on each; a literal `**Proof sketch.**` on every proof over 20 lines (`policy.md` §3); public-facing docstrings (the user's rule; the precedent's region (d)); and, for a hand-built machine, a docstring "saying so and naming what was missing" (`policy.md` §1, **Construction reuse**). The draft's region (d) covers only the status text | policy.md §1, §3; precedent brief region (d) | Add to region (b): "Every new declaration has a docstring, and every proof over 20 lines a literal `**Proof sketch.**` paragraph (`policy.md` §3). Docstrings are public-facing library text: no campaign labels, dates or session narrative; provenance goes in `REPORT.md`. The replay leaf's docstring says which public rows it is not and what was missing (`policy.md` §1): `scanTM` reads one tape, and `StepBlock`'s `recordTM` reads records on `k + 2` tapes." REPORT checklist: add "each hand-built machine's docstring names the row it is not". |
| F8 | minor | 157–159, 160–162, 338–339, 348 | "copy it as a private" for `nfr_setup`/`nfr_pack` contradicts rule 11's "new privates under the `nf_` prefix" (`nfr_` is not `nf_`) | — | "copy it as the private `nf_setup`" / "`nf_pack`"; checkpoint 1 "`nf_setup` and `nf_pack` copied" |
| F9 | minor | 183–187, 346–347 | The controller is not pinned, and the claim "a stopped stream is complete records, only the last flagged" depends on it. An initial flag `true` stops on the empty stream. The converse (stopped ⇒ `n ≥ 1` complete records, only the last flagged), which `hV` and the backward transfer use, is in no checkpoint | (b) above | After "`Q := Fin W × Bool` (…)" add "with `q₀ := (0, false)`, `δ (p, f) b := if p = W − 1 then (0, b) else (p + 1, f)` and `stop (p, f) := (p = 0 && f)` (the flag is the record's last bit)". Checkpoint 1: "…, and that a display first stops the controller at its end, and conversely that a stream which first stops it at its end is `n ≥ 1` complete records with only the last flagged" |
| F10 | minor | 412–422 | Hazard not named: "two configurations with the same input head read the same symbol", across machines, which the input sweep needs to transfer its checks to `N`. It exists only as the privates `xr_inputSymbol_congr` (ExhaustiveReplay:200, in the population, same statement) and `zr_inputSymbol_congr` (ZoneRebalance:14743). A fill copy will pair with `xr_`'s | out/07-dup-search.txt; out/NFReviewDupProbeRaw.out | Add a hazard: "the input read's congruence (equal input positions ⇒ equal `inputSymbol`, any tapes and states) is private in `ExhaustiveReplay` (`xr_inputSymbol_congr`) and `ZoneRebalance` (`zr_inputSymbol_congr`): state it once (from `Cfg.inputSymbol_of_zero`, `_of_end`, `inputSymbolInner`) and list it as a promotion request" |
| F11 | minor | 381–388 | `Build/Contract/Catalog` and `Build/Contract/Basic` are listed as "files the route cites", but neither is in the overlay's 26-module closure, so the route cannot cite them (the contract forms `scanTM_contract`/`clearTM_contract` live there). `TuringMachine/ChoiceReplay` (an NDTM's run along a choice word read from a tape, `replayTM_runFrom`) is a hazard for the backward induction and is absent | out/overlay-import-closure.txt | Move the two `Contract` files to the hazards ("the contract forms of the rows; outside your imports"). Optionally add `TCSlib/Complexity/TuringMachine/ChoiceReplay.lean` (re-measure the base: 21 files) |
| F12 | minor | 218–222 | The forward bullet folds three obligations into "`V` accepts it with an empty output". The forward lemma also needs `V` at neither `acc` nor `rej` before `TQ` | NDHost:1942–1966 | "…; `s` first stops the controller at its end (`hslive`, `hsstop`); `V` is at `acc` at `TQ` (`hacc`), at neither `acc` nor `rej` before (`hfirst`), with an empty output (`hnil`); `TQ = O(k · W · t₀)`; …" |
| F13 | note | 205–215, 223–228 | Route shape (recommended): give each leaf's run lemma as "after `r` records, a pure fold of the stream" (as `scanTM_run_ofCfg`), and `V`'s lemma as a characterization (first verdict at `T(s)`, `acc` iff every fold passes). That lemma is `hV`, the forward `hacc`/`hfirst` and the backward "acc ⇒ all passed" at once; the transfers then never touch a machine. Also, the target's frozen sketch (53–58) puts the state and the action record in the display, which the route recomputes (D3). Name the refinement, as the precedent does, so the maintainer re-synchronizes the sketch at landing (`policy.md` §3, **Synchronization**) | out/NFReviewVProbe.out | Add after line 116: "This brief refines the docstring's sketch in one place: the display carries the choice bit, the claimed reads and an end flag; the state and the action are recomputed, never guessed (ruling D3)." |
| F14 | note | 496–514 | Pitfall to add: with `GuessRunPhase.CtlState` sealed, `CtlState SP SQ Q .run` does not reduce to `SQ`, so no term naming a host state (`⟨.pre, P.q₀⟩`, `Sigma.mk .run`) elaborates. The route needs none | out/NFReviewSealControl.v1.out (line 132); out/NFReviewProbe.out | "Under the seal, never write a host state yourself: cite only `guessCtlRunTM_accepts_of` and `guessCtlRunTM_stream_of_accepts`, whose statements name none (the review's sealed `rv_skeleton`)." |
| F15 | note | 302–307 | The own-leaf allowance and the seal are compatible only for *explicit* unfolding: `unfold MultiTapeTM.step`/`simp only [Action.apply]` passes `local irreducible`, while `show`/`change`/`rfl` through them fails | out/RVUnfoldUnderSeal.out | Append: "An own leaf's unfolding is by `unfold`, `rw` or `simp only` with the definition (listed in the inspection table), never by `show`, `change` or `rfl` (the seal rejects those)." |
| F16 | note | 506–507 | Pitfall "the acceptance lemmas take the stream after the setup's `TP + 1` bits … one dispatch bit" is internal to the host. `accepts_of` returns `∃ w`, and `stream_of_accepts` returns `∃ s`; the fill never builds or splits `w` | out/NFReviewProbe.out (`rv_skeleton`) | Delete, or: "The acceptance lemmas hide the word: the forward one returns it, and the backward one returns the stream." |
| F17 | minor | 80–84 | The in-flight list is incomplete. **#177** (H's NP closure, opened after the draft, base the campaign branch) changes `ClassNP/Reductions.lean`, which is in your order list (position 45) as an import of the downstream `ClassNP` facade. Also name **#176** for E-Q cont1's landing (only `NTimeDiagonalizer`), which is in the list as an import of the downstream `NTimeHierarchy`, not "as a downstream module" | out/09-open-prs.txt; out/03-order-check.txt | "**In flight, merging after your base and invisible to it:** E-Q cont1's landing (PR #176, `Diagonalization/NTimeDiagonalizer`, in your order list as an import of the downstream `NTimeHierarchy`; …) and H's NP closure (PR #177, `ClassNP/Reductions`, in your order list as an import of the `ClassNP` facade; …)". Re-take the line at issue, for whichever PRs are then open |
| F18 | note | 164–166 | The packaging needs only `Fintype` (`Fintype.equivFin` takes no `DecidableEq`). `DecidableEq` is needed on `V`'s state type (`guessCtlRunTM`'s `[DecidableEq SQ]`). The fold's and the leaf's state types must therefore be finite with decidable equality: records as `Fin`-indexed functions, not lists | out/RVShapes.out | "…by the published instances; `V`'s state type, and so the fold's and the leaf's, must be a `Fintype` with `DecidableEq` (hold a record as `Fin _ → Option Bool`, not a list)." |
| F19 | note | 179–180, 234–243 | A 2-bit block has a fourth code; the claimed read needs a total meaning for it (reject in sweep 0, or decode to a fixed value) | — | Edge case: "a claimed-read block with the unused code: sweep 0 rejects it (or it decodes to `none`; say which)." |
| F20 | note | 205–209 | A reviewer may read the tape-replay leaf, which replays a fixed machine's actions on a tape, as an "interpreter or simulation step block" (`policy.md` §1, a host). The design note's table assigns the sweeps to NF as own-file leaves, and D2 ruled only the guess-run host into `NDHost` | NF-route-design.md (Leaves and sizes; D2) | Add: "The sweeps are own-file leaves by the design note (its 'Leaves and sizes' table; D2 moved only the guess-run host to `Build/NDHost`): their contract is this file's display format, and no other consumer exists." |

Counts: 2 major, 11 minor, 7 note.

## Appendix A: replacement text for F1 and F2

**A1 (F1).** Hosts bullet, 167–170: replace "over your own leaves, `Turing.skipBackTM` (A's rewind,
`skipBackTM_run_ofCfg`) and `Turing.inputRewindTM` (the input head's return, `inputRewindTM_run`,
`_step_done`)" with:

> over the published rows `Turing.scanTM` (sweep 0: `scanTM_run_ofCfg`, `scanFold`, `scanKeep`,
> `scanResult_fold`), `Turing.skipTM` and `Turing.skipBackTM` (`skipTM_run_ofCfg`,
> `skipBackTM_run_ofCfg`: the returns of A and B), `Turing.clearTM` (B's clear,
> `clearTM_run_ofCfg`; not the R3 row `clearTM_run`) and your one replay leaf

Line 189: "**`V`'s phases**, each followed by A's rewind:" → "**`V`'s phases** (A's head is back at
cell `0` after each):"

Item 1, 190–193, replaced by:

> 1. **Sweep 0**, the control check, is **the published scan fold** on A:
>    `Turing.scanTM 2 0 (scanFold δ₀) scanKeep a₀`, with your fold step `δ₀` over the stream's bits.
>    From the entry it reaches `done (s.foldl δ₀ a₀)` at exactly `2|s| + 2`, no `done` earlier, with
>    every tape and head as at the entry, so A needs no rewind (`scanTM_run_ofCfg`,
>    `scanResult_fold`). `δ₀`'s state (a `Fintype` with `DecidableEq`) holds:
>    - the position in the record and the record read so far;
>    - `qᵣ`, from `N.tm.q₀`;
>    - the output summary, from `outputSummary [] = none` and updated by `summaryEmit`;
>    - a failure flag.
>
>    At each record's end it recomputes `aᵣ` and checks that `endᵣ` is set exactly when
>    `aᵣ.state = none`. Its verdict passes iff no check failed and the final summary is
>    `some true` (`outputSummary_true`: exactly `[true]`). **Write no machine for sweep 0.**

205–209, replaced by:

> **One leaf for sweeps 1 to `k + 1`.** They share the record scan and the recomputation: write one
> leaf parameterized by the tape it replays (the input, or work tape `j` on B), not `k + 1` copies.
> It is a single own-file machine reading A one cell per step (A stationary while it works on B),
> with its run lemma by induction over records through `MultiTapeTM.step_of_some` and the
> `Action.apply_*` field equations; no private loop driver.

**A2 (F2).** Sweep 3's last sentence (202), "Then B is cleared over the visited region.", replaced
by:

> Then B's head goes to the visited region's first cell and B is cleared, by three published rows
> on B:
> 1. `skipTM` (over the region from B's head, `skipTM_run_ofCfg`; it leaves the head one past the
>    region's right blank);
> 2. `skipBackTM` (`u :=` the whole region, `skipBackTM_run_ofCfg`);
> 3. `clearTM` (`clearTM_run_ofCfg`), which leaves B blank with its head at the region's first
>    cell.
>
> The region is never empty: every record writes its block.

New paragraph after item 4 (204):

> **A's return after a replay sweep.** A replay sweep ends with A's head on the blank after `s`
> (cell `|s|`). `skipBackTM_run_ofCfg` needs the head **one cell past** that blank, so first step
> right with `skipTM` on A (`skipTM_run_ofCfg` at `w := []`), then run `skipBackTM` on A at
> `u := s`, as the host does after its writer. `Build/Rewind`'s `rewindTM`, which starts on the
> blank, is outside your imports.

`hV`'s sentence (213–215), "Each sweep ends at the blank after `s`, B's replay moves its head at most
two cells per record, and B's clear ends at the visited region's edge, so `V` is total", replaced
by:

> Each replay sweep ends at the blank after `s` or rejects earlier; B's replay moves its head at
> most two cells per record; and B's clear (`skipTM`, `skipBackTM`, `clearTM`) runs over the
> visited region, which is contiguous and nonblank on every stream. So `V` is total

## Appendix B: what the fill's `V` looks like with F1, F2 and F4

The phases are:
1. `scanTM` (sweep 0);
2. the replay leaf in input mode, then `skipTM` A and `skipBackTM` A;
3. per `j < N.k`: the replay leaf in tape-`j` mode, then `skipTM` A, `skipBackTM` A, `skipTM` B,
   `skipBackTM` B and `clearTM` B;
4. a verdict park whose states are `acc` and `rej`.

Every exit is redirected by one silent `phaseHostTM` step. A failed check goes to `rej`.
`NFReviewVProbe` checks the first and last phases of this shape sealed. The time is:
- `2|s| + 2` for the scan;
- at most `(W + 4) · n + 1` per replay, where `n = |s| / W` is the record count;
- `|s| + 4` per A return (`skipTM` 1, `skipBackTM` `|s| + 3`);
- at most `8(n + 1) + 6` per B clear (`4|u| + 6` for a region of `|u| ≤ 2(n + 1)` cells);
- one step per redirect.

So `TQ = O(k · W · t₀)`, and `C := 2W + c₁ (k + 2) W + c₂` meets `0 + 2|s| + TQ + 11 ≤ C (t + 1)`
for `t₀ ≤ t`.
