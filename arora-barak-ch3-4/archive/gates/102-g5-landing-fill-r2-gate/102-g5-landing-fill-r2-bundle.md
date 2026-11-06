## ===== campaign/gates/102-g5-landing-fill/pack-r2.md =====

# External audit pack, round 2: G5's landing, `Turing.FinTM.two_work_tapes_run` (PR #211, a fill gate)

**Round 1** (`pack.md`; findings `findings.md`; dispositions `resolutions.md`) was **HOLD, 0
blockers, 1 major, 1 minor, 5 notes**, with no soundness defect. Notes 3–7 verified the bundle,
the frozen statements, the boundary cases, the amortization, the seal and axiom evidence, the
landing repairs and the screen. The issues were:
- **Finding 1 (major):** `tt_forward_run`'s zero-time branch re-derived the imported
  `FinTM.not_computesInTime_zero`;
- **Finding 2 (minor):** `two_work_tapes_run`'s sketch said "each zone is kept half full", which
  misstates the invariant.

**The PR:** #211 on `lean/u2s-g5-landing`, head `e7e78aaf` (full hash in the bundle header):
round 1's head `f239dafd`, the repair `3a261ba2`, and a records-only merge of the campaign. One
file, `TwoTapes.lean`.

## What changed since round 1 (verify)

| Finding | Change (`3a261ba2`; `evidence/round2/round2-edits.diff`) |
|---|---|
| 1 | **Fixed** (the user's standing rule: a mechanical re-point in the PR). The branch is `exact not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)`, the auditor's proposed fix. A search of the library for the impossibility's other closing forms (`initCfg_eq` and `Cfg.init_state` rewrites ending in a contradiction) finds deterministic sites that already cite the lemma (`ClassP/DTIME`, `ClassNP/TMSAT`, `CookLevin/Hardness`, `Diagonalization/EXPCOM`) and two NDTM analogues with no published lemma (`ExhaustiveReplay`'s private `xr_not_haltsWithin_zero`, an inline step in `NDNormalForm`). The latter are outside #211 and recorded in the ledger as **NZ-1**, a promotion candidate awaiting the user |
| 2 | **Fixed.** The sketch: each side of a level is empty, half full or full, the two sides of a level hold a constant total, and a rebalance at index `i` restores every level below `i` to half full |

The freeze against round 1's head: only `tt_forward_run`'s body and `two_work_tapes_run`'s
docstring (`evidence/round2/freeze/`).

## Brief for the auditor

1. **Findings 1 and 2:** are both fixed, and is the NZ-1 search adequate?
2. **The repair itself:** does it change anything beyond the findings?

## Repository-side attestations (verify or challenge)

- **Replay** (`evidence/round2/merged-tree/`): `replay-lg7` at `e7e78aaf`, `TwoTapes`,
  `UniversalTlogT` and the `TuringMachine` facade, chained from the campaign's `oleans-lnth`:
  **3 modules, 0 failed, 0 `sorry`**; static 0 mismatches.
- **Rule 10** (`evidence/round2/seal/`): round 1's generator and 44-definition list re-run on the
  head's file: the sealed copy elaborates with **0 diagnostics** on `oleans-lg7`; controls **91
  pass unsealed, 91 fail sealed**.
- **Axioms** (`evidence/round2/seal/`): `two_work_tapes_run`, `two_work_tapes_binary` and
  `Turing.universal_TlogT` on `[propext, Classical.choice, Quot.sound]`; all 104 declarations
  within those three, no `sorryAx`.
- **Screen** (`evidence/round2/screen/`): the 22-file population at the head: **1,277 declarations, 840 pairs,
  288,323 characters**, identical to round 1's (0 new, 0 gone).
- **Lint** (`evidence/round2/lint/`): unchanged from round 1 (0 FAIL, 72 WARN over 92 files; the
  policy linter's one finding, the size).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/102-g5-landing-fill/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `g5-landing-fill-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.

## ===== campaign/gates/102-g5-landing-fill/findings.md =====

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean:1599–1603` · `tt_forward_run`; `evidence/sweep/README.md:140` | The zero-time branch re-derives the imported `FinTM.not_computesInTime_zero`; the sweep's “no composite lemma” disposition misses it. This is duplication debt, not a soundness error. | `Finite.lean:350–353` already proves that an initialized machine cannot compute in zero steps. After the existing `h0`, `computesInTime_iff` constructs precisely such a computation by choosing its actual output. The subsequent `runFrom_zero` / `initCfg_eq` / `Cfg.init_state` rewrite and contradiction reproduce the published impossibility argument. RO-1 concerns one-step runs, FH-1 concerns extracting a first halt, and NF-X1 excludes initial-field transports without a matching composite; none acknowledges this copy. | Replace the last two lines of the branch by `exact not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)` and correct the sweep disposition. If retained, **human acknowledgment required**, with a named resolution. |
| 2 | minor | `TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean:2421` · `two_work_tapes_run` docstring | “Each zone is kept half full” incorrectly states the invariant. | `tt_full` permits each side to be empty, half full, or full. For a one-track machine's first live right move, extension creates one stored blank on each side of level 0; `zoneCascadeRight_lengths` then gives left length `1 + 1 = 2` and right length `1 − 1 = 0`. Only levels strictly below the scanned index are reset to half full. This also agrees with [AB09, §1.7, pp. 31–32](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf). | State the empty/half/full invariant and the constant combined occupancy of each left/right pair; say that rebalancing restores half fullness strictly below its scanned index. |
| 3 | note | Bundle, pinned sources, public declarations | Integrity and statement freeze verified. | Bundle SHA-256 is `a79385da1ad4331dcb6559207ddcfcb29e1ab4dced93f4734015eaf068f0582d`; all 89 sections were checked against their pins: 22 Lean files at `f239dafd09f060ec87ca0992103ae8eb48bce31e`, 67 records at `f6954560434dbf5c4a7777f29f1c481cee151f92`. Both public statements are unchanged; `two_work_tapes_binary`'s proof is unchanged. The Lean diff changes only `TwoTapes.lean`, with 102 private declarations added. | None. |
| 4 | note | `TwoTapes.lean` · `tt_zero_tapes`, `tt_forward_run`, `tt_cs_halt`, `tt_track_seg`, `tt_converse`, `tt_frame` | No boundary-case or converse defect found. | Zero tapes use the empty forwarding embedding with constant 1. Zero-step halting is impossible in this model. A halt on the first transition takes one zone-machine step, including any final output emission, without track phases. Stays have zero contract time but retain their dispatch step. A nonhalting source supplies live segments beyond every proposed simulator halt. The alphabet-reduction converse is used with the required image-output witness; empty inputs are covered by the lifted input-symbol equation. | None. |
| 5 | note | `TwoTapes.lean` · `tt_count`, `tt_D_level`, `tt_idxR_le`, `tt_cost` | The count, level bound, and final cost fit the published amortization API. | The side total resets to its midpoint after a large-index step and drifts by at most one between such steps. The resulting gap supplies `tt_count`. The displacement invariant bounds the power of the level count by twice the elapsed source time plus one, yielding `tt_idxR_le`'s logarithmic cutoff. `tt_cost` applies `sum_cost_le_of_count` with both hypotheses and obtains its stated constant; `tt_frame` multiplies it by the alphabet-reduction constant. The zero-horizon index statement is vacuous. | None. |
| 6 | note | `evidence/seal/`, `evidence/axioms/`, `evidence/merged-tree/` | Rule-10 and axiom evidence is consistent with the pinned source. | The sealed copy is exactly the pinned file plus the 44-definition seal and three simp removals. Both control sources match that seal; the logs cover the same 91 controls, all passing unsealed and failing sealed. Axiom output covers all 104 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. The downstream replay reports three successful modules, no sorry warnings, and zero static mismatches. These are checked repository attestations; I did not independently rerun Lean elaboration. | None. |
| 7 | note | `TwoTapes.lean`; duplication ledger; `evidence/screen/` | The recorded landing repairs are present; finding 1 is an additional semantic omission. | `tt_output_map` and `tt_sum_range_fin` are gone; their consumers cite the published lemmas. The input-symbol proof uses `SymbolLift`, and track phases use `Contract.inPhase` and `Contract.zero`. Fullness consumers reuse `tt_full_pre_*`. The ledger accounts for the surviving RO-1 site as 1 of 104 declarations. I independently reran the 22-file screen and reproduced it exactly: 1,277 declarations, 840 pairs, 288,323 characters. Its 21 additions over the base are internal to `TwoTapes`, with maximum overlap 89%; it does not detect the semantic duplication in finding 1. | Resolve finding 1; retain the existing dispositions for the other reviewed cases. |

**Verdict: HOLD — 0 blockers, 1 major, 1 minor. No soundness defect found; the gate remains open until finding 1 is removed or explicitly acknowledged with a named resolution.**

## ===== campaign/gates/102-g5-landing-fill/resolutions.md =====

# Gate 102 (#211, G5's landing): resolutions

## Round 1 findings (received 2026-11-06)

`findings.md`, verbatim (attached in chat by the user), SHA-256
`14003c5128fc921abce2639ec23365c2f6d477c5c41fb648e3adcd765de568bb`.

**Verdict: HOLD — 0 blockers, 1 major, 1 minor, 5 notes.** No soundness defect.

| # | Severity | Disposition |
|---|---|---|
| 1 | major | **Fixed** (the standing rule, WORKFLOW §3: a mechanical re-point in the PR). `tt_forward_run`'s zero-time branch is `not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)`. A search of the library for the impossibility's other closing forms (`initCfg_eq, Cfg.init_state` rewrites ending in a contradiction) finds only deterministic sites that already cite the lemma (`DTIME`, `TMSAT`, `CookLevin/Hardness`, `EXPCOM`) and two NDTM analogues (`ExhaustiveReplay`'s private `xr_not_haltsWithin_zero`, an inline step in `NDNormalForm`), which have no published lemma and so are not members; they are recorded in the ledger as a promotion candidate. The sweep's disposition is corrected in this file. |
| 2 | minor | **Fixed.** `two_work_tapes_run`'s sketch states the invariant: each side of a level is empty, half full or full, the two sides of a level hold a constant total, and a rebalance at index `i` restores every level below `i` to half full. |
| 3–7 | note | No change. |

## ===== campaign/gates/102-g5-landing-fill/pack.md =====

# External audit pack: G5's landing, `Turing.FinTM.two_work_tapes_run` (PR #211, a fill gate)

## Why this PR

`Turing.FinTM.two_work_tapes_run` (`TuringMachine/Robustness/TwoTapes`; [HS66], as used in
[AB09, §1.7] for the efficient universal machine) was the campaign's last `sorry` in the
`TuringMachine` layer: every binary machine has a binary two-work-tape equivalent that reproduces
each halting run of `t` steps within `O(t log t)` steps. It closes `two_work_tapes_binary` and
`Turing.universal_TlogT` ([AB09, Theorem 1.9]). The fill G5 (brief
`campaign/fills/u2s/briefs/u2s-fill-g5.md`, agent Claude; REPORT
`campaign/fills/u2s/reports/g5-REPORT.md`) proves it with the frozen statement. Its API is gates
97 (#197), 98 (#202) and 99 (#207).

**The PR:** #211 on `lean/u2s-g5-landing`, head `f239dafd` (full hash in the bundle header):
- the delivery `fill/u2s-g5` at `71046be0` (base `335d31d4`, 15 commits, kept as delivered;
  `evidence/delivery/`), merged with the campaign at `3d0d9f86`;
- the maintainer's landing edits `c00340d4`, `794ffb48` and `f239dafd` (`evidence/landing/`),
  from a review of the delivery (`evidence/review/REVIEW.md`) and a have-level library sweep
  (`evidence/sweep/`);
- a records-only merge of the campaign, `87f7b193`.

It changes one file, `TwoTapes.lean`: 86 → 2,459 lines, 2 public (unchanged statements) and 102
private `tt_` declarations.

## What changed (verify)

| Declaration | What |
|---|---|
| `Turing.FinTM.two_work_tapes_run` (frozen statement) | proved; the one authorized body change. Its docstring's sketch names the zones `0, …, log₂ t + 1` (was "the `log₂ t + 1` zones") |
| `Turing.FinTM.two_work_tapes_binary` | unchanged; now on the standard axioms |
| 102 private `tt_` declarations | the zone simulator: the phase host, the zoned tape `0` and scratch tape `1`, the per-track steps, the fullness invariant, the side-total count and the cost sum |
| the imports | `Mathlib.Data.Fintype.BigOperators` and `TCSlib.Complexity.TuringMachine.SymbolLift` added at landing (both ruled by the user, below) |
| the module docstring | an Implementation notes section, the deviations for `k = 0` and the zone alphabet, and the size reason, added at landing |

**The landing edits** (no public statement changes):
- **The sweep's 15 hits** (`c00340d4`; `evidence/sweep/README.md`, copy D):
  - the private `tt_output_map` (core `Option.toList_map`) and `tt_sum_range_fin` (Mathlib's
    `Fin.sum_univ_eq_sum_range`, with the new Mathlib import) deleted: the review's two majors;
  - `StrictMonoOn.injOn`, `Finset.card_le_card_of_injOn`, `Finset.card_nsmul_le_sum`,
    `Fin.val_ne_of_ne` (four sites), `Fin.elim0`, `le_mul_of_le_of_one_le`,
    `Option.ne_none_iff_exists'`, `Finset.card_fin` and `Nat.nsmul_eq_mul`;
  - the borderline class (as in #208's sweep): `eq_of_le_of_not_lt` (two sites),
    `Nat.exists_eq_add_one`, `pow_succ'` (three sites), and `tt_Dtr_level_mono` through
    `monotone_nat_of_le_succ`.
- **The review's N2, N4 and F9** (`794ffb48`): `tt_full_pre_true`/`_false` package the full
  hypothesis set of `zoneCascadeRight_lengths`/`zoneCascadeLeft_lengths`, and
  `tt_full_rebalance_*`, `tt_rsum_rebalance_*` and `tt_tape_rebalance` cite them; the module
  docstring; `tt_count`'s sketch states the gap the proof uses (`2^{i+1} − 1 ≥ 2^i`).
- **The review's F6 and F5** (`f239dafd`, both ruled by the user):
  - F6: `tt_inputSymbol` is `Cfg.inputSymbol_congr` at the lifted configuration and
    `Cfg.liftSymbols_inputSymbol` (`SymbolLift`, now imported);
  - F5: `tt_track_seg` no longer re-walks `Build/Contract/Seam`'s private `inPhase_traj`. The new
    private `tt_phase_seg` builds the public `Contract.inPhase` for a track's phase (with the new
    `tt_next_ne`), and `tt_track_seg` applies it to `Contract.zero` for a stay and to the track
    step's contract for a move.

## Known deviations and dispositions (for the audit)

- **The two new imports** (the user, 2026-11-06: keep the Mathlib import; import `SymbolLift`).
  The fill's brief froze the imports; both are maintainer landing edits that remove a copy.
- **ZP-1 is not cited** (the review's F4): each phase starts at a configuration built at its own
  state type, and each endpoint is converted through `zoneRowPre_iff` and RN-1's
  `Cfg.mapState_eq_of_fields`. Nothing re-derives the state-independence; the maintainer accepts
  the route (`campaign/duplication-ledger.md`, ZP-1).
- **RO-1 +1** (the review's N3): `tt_round` closes the one-step identity inline; the ledger's
  RO-1 counts it for the dedup window.
- **The mirror pairs** `tt_full_pre_*`, `tt_full_rebalance_*`, `tt_rsum_rebalance_*`
  (`dir = true`/`false`) stay: the closure publishes no swap equations for `zoneShiftIndex` or
  `zoneRebalance`, and the side totals differ in sign.
- **Size** (2,459 lines; the style lint's one new WARN, the policy linter's one finding): one
  construction and its correctness proof, whose lemmas concern the simulator's own definitions;
  the brief sets no cap. The module docstring states the reason.
- **The REPORT's errata** (the review's F3, F6–F10): the inspection table is incomplete (F3; the
  review re-extracted all 560 bracketed arguments: no rule-10 violation); the semantic search is
  by family, not per private (F6); the extended import probe's output, `UniversalAxioms.lean` and
  `Probe2` were not shipped, and the "307 checks" count includes non-names and a duplicate (F7);
  the checkpoint zips cp6 and cp7 are absent (F8); §8's "departure" sentence is wrong, since the
  count proves exactly the sketch's bound (F9); `workTapePos_runFrom_mem_Icc` and the unprimed
  `runFrom_succ_eq_step` are used without listing (F10; both proved public theorems, confirmed).

## Brief for the auditor

1. **Soundness and pins:** is `two_work_tapes_run`'s statement frozen, and is the proof correct,
   including `k = 0`, runs that halt at once, and the zone level bound?
2. **Rule 10:** do the proofs read other files' definitions only through published equations?
   The seal and its controls are below.
3. **Duplication:** does any proof still re-derive a published lemma (typed or untyped `have`,
   `simp` set, rewrite chain, conjunct), or another file's private? The review and the sweep list
   every candidate with a disposition. Challenge any.
4. **Public text:** are the module docstring and `two_work_tapes_run`'s docstring accurate, free
   of campaign labels, and attributed?

## Repository-side attestations (verify or challenge)

- **The delivery** (`evidence/delivery/`): `SHA256SUMS`, the REPORT's hash, the final logs and
  both screen outputs; the bundle and patch series checked against the source by the maintainer.
- **Rule 10** (`evidence/seal/`): the delivery's generator `mkseal.py` re-run on the head's
  `TwoTapes.lean`, with the delivery's 43 definitions and `Turing.Cfg.liftSymbols` (now read
  through `SymbolLift`'s equations): **44 sealed**, plus `[-simp]` on the three `@[simp]`
  definitions of the closure. The sealed copy elaborates with **0 diagnostics** against
  `oleans-lg6`; the controls: **91 pass unsealed, 91 fail sealed**.
- **Axioms** (`evidence/axioms/`, on `oleans-lg6`): `two_work_tapes_run`, `two_work_tapes_binary`
  and `Turing.universal_TlogT` on `[propext, Classical.choice, Quot.sound]`; all 104 declarations
  of the file within those three, no `sorryAx`.
- **Freeze** (`evidence/freeze/`): against the campaign, 2 → 2 public, 0 → 102 private,
  `two_work_tapes_run`'s body the one authorized change; against the delivery, 102 → 102 private
  (`tt_output_map`, `tt_sum_range_fin` removed; `tt_phase_seg`, `tt_next_ne` added).
- **Screen** (`evidence/screen/`): the brief's 22-file population on a `git archive` of the head:
  **1,277 declarations, 840 pairs,
  288,323 characters**. Against the delivery's after-screen (843 pairs): 0 new, 3 gone (the two
  `tt_full_rebalance_*`/`tt_full_pre_*` pairs that N2 removed, and `tt_Dtr_other` against
  `tt_Dtr_level_mono`). Against the base's before-screen (819 pairs): 21 new, every one between
  two `TwoTapes` declarations, the largest 89% (`tt_D_inv` against `tt_D_succ`); no cross-file
  pair, none at 90%. The left/right mirrors are among them (above).
- **Lint** (`evidence/lint/`): the campaign lint on `TuringMachine` 0 FAIL, 72 WARN over 92 files
  (71 at the base; the new WARN is `TwoTapes`' size); the policy linter 1 finding, the size.
- **Replay** (`evidence/merged-tree/`): `replay-lg6` at `f239dafd`, the downstream closure of
  `TwoTapes` (`TwoTapes`, `UniversalTlogT`, the `TuringMachine` facade), chained from the
  campaign's snapshot `oleans-lnth`: **3 modules, 0 failed, 0 `sorry`**; static 0 mismatches.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/102-g5-landing-fill/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `g5-landing-fill-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.

## ===== campaign/gates/102-g5-landing-fill/STATUS.md =====

# Gate 102 (#211, G5's landing: `Turing.FinTM.two_work_tapes_run`)

- 2026-11-06: the delivery received (`71046be0`, base `335d31d4`), reviewed by a sub-agent
  (`evidence/review/REVIEW.md`: 0 blockers, 2 majors, 8 minors, 6 notes) and swept at the have
  level (`evidence/sweep/`: 15 hits). #211 opened at `3d0d9f86`.
- 2026-11-06: the landing edits `c00340d4` (the sweep; the Mathlib import, ruled by the user),
  `794ffb48` (N2, N4, F9) and `f239dafd` (F6 through `SymbolLift`, F5 through `Contract.inPhase`,
  both ruled by the user). `replay-lg6` passed (3 modules, 0 failed, 0 `sorry`); the seal (44),
  controls (91/91), axioms, freeze and lint in `evidence/`. The screen: 0 new pairs against the delivery, no cross-file pair. Pack complete.
- 2026-11-06: staged (`outbox/gates/102-g5-landing-fill-gate/`, exchange commit `047920ad`):
  bundle `102-g5-landing-fill-bundle.md`, 89 sections, SHA-256
  `a79385da1ad4331dcb6559207ddcfcb29e1ab4dced93f4734015eaf068f0582d`; Lean from `f239dafd`,
  records from `f6954560`. Findings file `g5-landing-fill-findings.md`.
- 2026-11-06: **dispatched** (the user).
- 2026-11-06: round 1 findings received: **HOLD 0/1/1** (F1 `not_computesInTime_zero`, F2 the
  invariant's prose). Both fixed on #211 (`3a261ba2`; the standing re-point rule); NZ-1 recorded.
  `replay-lg7` passed (3 modules, 0 `sorry`) at `e7e78aaf`; the seal (44), controls (91/91),
  axioms, freeze, lint and screen re-run (`evidence/round2/`). `pack-r2.md`.

## ===== campaign/standards/TEMPLATE.md =====

# External audit pack — TEMPLATE

Copy this file to `audits/phaseN-pack.md`, fill every `⟨…⟩`, and hand the result (plus
the listed attachments) to an external LLM from a different vendor, in a fresh context
with no access to this repository's development history. Record the findings in
`audits/phaseN-findings.md`. A phase's findings must be addressed (fixed, or explicitly
waived with a reason) before the next phase begins.

---

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`,
   `k = 0` tapes, constant absorption).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (per-file copied-material
   totals) rather than assessing each copy in isolation.

   **Accounting inside an acknowledged family is a minor.** Once the human
   maintainer has acknowledged a debt family and named its resolution, a later
   correction to that family's *accounting* is reported at **minor**, not major.
   Examples are a missed member, a miscounted span, or an imprecise description of
   the screen. Such a correction does not change what was approved. It is a
   **major** again only if it changes the approval itself: the correction pushes a
   further file past the one-fifth threshold, reveals copies outside the
   acknowledged family's named scope, or shows the named resolution cannot work.

**Seals and reducible abbreviations.** A rule-10 seal (`attribute [local irreducible]` on
other-file definitions, each with an `rfl` control that closes unsealed and fails sealed) cannot
include a reducible `abbrev`: Lean's default reducibility validation refuses the attribute (the
unsafe override `allowUnsafeReducibility` is not used in seals). `policy.md` (*Definitions
land with their lemmas*) allows reading an abbreviation through its body, so that is not a finding.
Do report an `abbrev` passed to `simp`, `rw` or `unfold` where a published lemma exists, and a new
public `abbrev` without its lemma.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least ⟨3⟩ *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends. Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Lean files under audit | ⟨list of files, with line ranges if partial⟩ |
| Source text | ⟨book/paper, edition, page/theorem numbers — auditor must have it at hand⟩ |
| Plan/context documents | `AroraBarakChapter1Plan.md`, `policy.md` §2-3 ⟨adjust⟩ |
| Out of scope | tactic proofs; vendored files' upstream design ⟨adjust⟩ |

## Known deviations (declared by the authors — verify they are benign, flag any others)

⟨Bulleted list: every deviation the docstrings declare, one line each.⟩

## Specific questions for this phase

⟨Numbered list of the doubts the authors actually have. Be concrete.⟩

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment (accounting corrections inside an already-acknowledged family are
minors; see failure mode 5); **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).

## ===== campaign/duplication-ledger.md =====

# Cumulative duplication ledger

The standing per-file accounting of copied proved material that
`workflow.md` §4 requires at every epoch boundary. Created as the
retrofit-R1 round-1 repair (R1-2); **rebuilt at round 2** (R2-1/R2-2 of
`audits/retrofit-r1-r2-findings.md`): the first version's arithmetic was
inconsistent (summands 261 against a printed 249), its inclusion rule was
applied asymmetrically, and it **misclassified an exact three-file copy
family as "design-harvest reimplementation"** — the round-2 auditor
proved the four relocation declarations byte-identical across `Loop`,
`Primitives`, and `Hardness` after consistent identifier substitution,
and found the 13 exact Loop-internal H3 copies omitted. This version
adopts one inclusion rule, enumerates every family, and uses the
auditor's independently computed figures wherever they exist.

## Counting convention (one rule)

**Primary rule — expanded correspondence membership**: a declaration is a
ledger member iff it belongs to a *recorded cross-declaration
correspondence* — the retrofit inventories' twin maps **including their
strengthened-counterpart rows**, the A2/F2A reports' declared copies, and
the round-2 audit's verified relocation and H3 families. Each member is
counted **once per file it inhabits**. (Secondary, where it differs: the
*strict normalized-byte-twin* count excludes the five strengthened
counterparts — Loop's `loopHost_prepare`/`loopHost_contracts`,
Primitives' `splitSolve_of_body`/`_source`/`_closed` — and H3's one
near-copy `_init` pair.) Fractions are members over the file's total
declarations. Line figures use the round-2 audit's span rule — attached
docstring and intervening closure note through the last code line,
excluding separating blank/module-note blocks — with the auditor's
computed values where available and estimates under the same rule marked
`≈`.

## State after retrofit epoch R1 (the merged PRs #9/#10)

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Lines in member blocks |
|---|---:|---:|---:|---:|---:|---:|
| `Build/Loop.lean` | 212 | 87 →Catalog (of the historical 95; strict 85) + 4 relocation originals (`emCallAction`/`emCallCfg`/`emCall_apply`/`emCall_relocate_run`, the batch-L source of the three-file family) | 13 H3 exact copies (`emLoopHost_*`; their `loopHost_*` originals are already in the 87 and are not double-counted; the `_init` and `_anchor_return` near-copies are counted as source-side members since round 7 — Catalog twins reproduce them cross-file) | **98** after RB4 (merged, PR #13 `b2833d46`; was 117 — generated, pass 4): 88 historical + 10 from pairs. RB4 deleted 12 H3 copies, the 4 relocation originals and `emLoopHost_init`; `emLoopHost_anchor_return` and `emLoopHost_start` no longer reproduce a Catalog proof after the agreement-transfer rewrite | **49.2%** (98/199) | **2,647** (was 3,153; both totals from the script's span routine, which reproduces the audited 3,153) |
| `Build/Primitives.lean` | 259 (272 before RB5) | 146 →Catalog (of the historical 150; strict 143) + **6 public originals** reproduced in Catalog (round-5 screen: `computesFunInTime_stripLast` → the adaptation `f2_strip_linear`; `_prepend`, `_pairEncodeFixed`, `_pairFst`, `_pairSnd`, `_pairConcat` → their strengthened `_spaceUsed` counterparts) | **none** — RB5 (PR #14, merged 2026-10-10) deleted the 4 relocation copies (`emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/`emitterP2_relocate_run`, formerly byte-identical to Loop's) | **168** after RB5 (was 173) — generated (pass 4): 145 historical (the 4 relocation members and the `splitEmbed_run` twin are deleted) + the same 23 sources of like-kind MEMBER pairs (the 6 round-5 publics, round-6 `emitterP2_control`, and 16 found by the complete round-7 pass: `emitterAppend_run`, `emitterP2EraseTM`, `emitterP2StateDecidableEq`, `emitterP2_erase_scan`, `emitterP2_prepare_rewind_candidate`/`_suffix`, `emitterSplit_find`/`_loop_bound`/`_of_body`/`_result`, `emitterTokenTM`, `emitterToken_double`/`_separator`, `emitter_first_entry`, `mapCfg`, `mapStart`) | **64.9%** (was 63.6%) | **3,790** before RB5 (3,415 + 375 round 7); not re-measured after it |
| `CookLevin/Hardness.lean` | 545 (549 before RB5) | 0 | **none** — RB5 deleted the 4 relocation copies (`clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run`) and `clMap_run`. Not copy debt, but recorded: its replacement certified-layout layer `clPlacement` is a private generic adapter, scheduled for dissolution as 12.2c item 13 | **0** (was 4) | **0%** | 0 (was 73) |
| `Build/Catalog.lean` | 428 (423 at the R1 close, plus the five §12.6 framed contracts) | 2 in-file originals (`f2_finSumEquiv`, `f2_sum_add` — their `a2_` copies are normalized-identical, round-3 verified) | 150 Primitives-sourced + 95 Loop-sourced + 17 Wrappers-sourced (10 `f2_timed*`, 7 `catalog_redirect*`) + 2 in-file `a2_` copies + **3 Composition-sourced** (`f2_idTM`, `f2_idTM_run`, `f2_constTM` — maintainer-reconciled normalized-identical to `Composition.lean`'s originals) + **20 counter-block members** (`f2_counterInc` … `f2_counter_computes` — maintainer reconciliation, declaration by declaration: **19 normalized-identical** to `ClassP/TimeConstructible.lean`'s originals, and `f2_counter_computes` a **near-copy adaptation** of the proof body of the public `timeConstructible_id`) + **7 strengthened public counterparts** whose time conjuncts reproduce a public source proof (`computesFunInTime_id_spaceUsed`/`_const_spaceUsed` ← `Composition.lean`, round 4; `_prepend`/`_pairEncodeFixed`/`_pairFst`/`_pairSnd`/`_pairConcat_spaceUsed` ← `Build/Primitives.lean`, round 5 — 89-100% of each source proof reproduced) + **2 F2A adaptations** of public proofs (`f2_strip_linear` ← `computesFunInTime_stripLast`, 86% of the source reproduced — round-5 finding R5-1; `f2_counter_heads` ← `timeConstructible_id`, 64% — round-5 screen) + **20 round-6 members** from the exhaustive screen: R6-1's `f2_counter_count_space` (80.3% of the private `counter_count`) and 19 further cross-file adaptations — 4 F2A (`f2_exists_loopFind_space` 97.8% of `exists_loopFindTM`, `f2_cond_time` 92.0% of Wrappers' `computesFunInTime_cond`, `f2_rewind_heads` 90.8% of `catalogRewind`, `f2_cond_ledger` 70.3% of `timed_start`), 13 A2 (`a2_map_block`/`_suffix`/`_backA`/`_backB`/`_parse`/`_setup`, `a2_mapVirtual_run`, `a2_mapSetup_stationary`/`_run`/`_heads`, `a2_call_run`, `a2_loop_prepare` 86.8% of `loopHost_prepare`, `a2_loop_round`), and 2 public rows (`computesFunInTime_pairLenCheck_spaceUsed` 71.4% of `computesFunInTime_pairFst`; `exists_loopTM_spaceUsed` 85.5% of `exists_loopCfgTM`, 81.0% of `exists_loopTM`) | **318** | **74.3%** (75.2% of 423 at the R1 close; strict — excluding the 34 strengthened counterparts/adaptations and the 1 near-copy: **283, 66.1%**) | **7,539** (6,267 round-4 measured + 224 round 5 + 52 R6-1 + 996 for the 19) |
| `Build/Wrappers.lean` | 29 (10 pub + 19 priv) | 17 + 1 round-6 source (the public `computesFunInTime_cond`) | 0 | **19** — generated (pass 4): 17 historical + `computesFunInTime_cond` (round 6) + `captureCfg` (round 7) | **65.5%** | **355** (297 + 40 + 18) |
| `ClassP/TimeConstructible.lean` | 21 | 20 (the 19 identical counter originals + `timeConstructible_id`, the source of both the near-copy `f2_counter_computes` and the adaptation `f2_counter_heads`; the private `counter_count` is likewise the source of R6-1's `f2_counter_count_space`) | 0 | **20** | **95.2%** (strict: 19, 90.5%) | 355 (round-4 measured) |
| `TuringMachine/Composition.lean` | 19 | 5 (`idTM`, `idTM_run`, `constTM` + the public `computesFunInTime_id`, `computesFunInTime_const` whose proofs the Catalog rows reproduce) | 0 | **6** — generated (pass 4): + `controlCfg_run` (R7-1) | **31.6%** (strict: 3, 15.8%) | **109** (97 + 12) |
| `Build/Embed.lean`, `Build/Seam.lean`, `Build/VirtualInput.lean`, `Build/Zone.lean`, `Simulation.lean` | — | 0 | 0 | 0 | 0% | 0 |
| `Codes2Tape.lean` (ZF-B/B2/B3, integrated 2026-10-10) | 49 (9 pub + 40 priv; B3 added 16 new, non-copy privates) | 0 | **23 format-specific adaptations** of `CodeParser.lean`'s / `MathlibBridge.lean`'s one-tape top layer (20 retargeted + `zfBParse_full`/`zfBCanonical`/`zfBCanonical_eq`; agent-measured 60–100% body share) — the 46 format-independent copies were deleted after the promotion (f171767f) | **23** | **46.9%** (strict 3, 6.1%) | 290 code lines (agent-measured) — over one fifth: `backlog.md` §1 CH34-D2, **ACKNOWLEDGED (user, 2026-10-10) → 12.2c tasklist item 8** |
| `Robustness/SingleTape.lean` (ZF-C2) | 100 | 0 | 0 — **3 in-file near-duplicates noted, uncounted** per the in-file convention (maintainer screen: `dgPos_move` 93.1% of `sweepPos_move`, `dgStart` 72.9% of `sweepStart`, `dgInput_read` 64.3% of `sweepInput_read`; the agent disclosed the first and third as borderline) | 0 | 0% | 0 |

**Reconciliation notes (rounds 3-4 repairs)**: the F2A report's 306
inventory entries decompose as **150 Primitives + 94 Loop + 10 Wrappers +
3 Composition copies + 20 counter members + 2 in-file originals + 7
adaptations (`f2_strip_linear`, `f2_counter_heads`, round 5;
`f2_counter_count_space`, `f2_exists_loopFind_space`, `f2_cond_time`,
`f2_rewind_heads`, `f2_cond_ledger`, round 6) + 20 nonmembers** (the
round-4 correction: the old "29 outside" wrongly included the two counted
in-file originals); the 20 share no member-level material with any
declaration of the five source files (round-6 exhaustive screen below) (the `f2_polyHeads`/`f2_space_of_time`/
`f2_segment_heads`-class engines and strengthenings — round-4 sampled and
accepted). The A2 report's 45 declarations contribute 2 in-file copies +
`a2_loop_halted_run` (in the Loop 95) + **13 cross-file adaptations**
(round-6 screen) + 29 new constructions. Catalog's union:
`318 = 286 F2A + 16 A2 + 7 earlier redirect + 9 public counterparts`.

**The public-proof screen (round-5 repair of R4-1; R5-1/R5-2/R5-3).**
Published as `audits/evidence/retrofit/r1-public-proof-screen.py` with its
output `r1-public-proof-screen.out`. *Erratum:* the round-4 run tested
whether a source proof was contained **whole** in its counterpart, but the
round-4 text described "segments ≥ 60 characters". The round-5 auditor ran
the method as described and found six fragment hits that the containment
test could not see. The method below is the one actually run.

- **Method.** Strip comments and all whitespace. Rename each source
  identifier `h` to `f2_h` wherever Catalog declares `f2_h` (dotted names
  split). Report two measures:
  - the **longest common contiguous segment** (LCS), with the literal ≥ 60
    candidate threshold;
  - the **shared length**: greedy string tiling with blocks of at least 25
    characters, as a fraction of the **source** proof.
- **Rule.** A pair is a **member** when at least half of the source proof
  reappears in the target, with an absolute floor of 60 shared characters
  so that a one-line citation of a public lemma counts as reuse. Any other
  shared tiling of at least 60 characters is a recorded **fragment**, not
  counted. The rest are citations or no match.
- **Population (R5-3).** 17 eligible pairs: 2 from Composition (`id`,
  `const`) and **15** from Primitives, not the 16 stated in round 4. Five
  source theorems have no `_spaceUsed` counterpart: `ifEq`, `comp`,
  `splitSolveWith`, `unaryToken`, `appendBit`.
- **Pass 1, direct pairs.**
  - Members (7): `id` 96.5%, `const` 97.1%, `prepend` 93.9%,
    `pairEncodeFixed` 100%, `pairFst`/`pairSnd` 88.8%, `pairConcat`
    88.7%.
  - Fragments, recorded and not counted (3): `polyUnary` (119 characters
    shared, 46.7%); `pairLenCheck` (305, 21.9%; its LCS is the 91-character
    `Nat.pow_one` bound); `stripLast` (221, 11.7%; its LCS is the
    121-character `have hn` weakening).
  - Citations or no match (7): `lengthBits`, `polyBits`, `pairValid`,
    `pairDup`, `pairMapSnd`, `splitSolve` (the auditor's 27-character
    citation), `incFixed`.
  - The literal ≥ 60 LCS screen reproduces the auditor's hit set exactly
    (`id` 776, `const` 273, and 62/75/75/75/91/121 for the six Primitives
    pairs). One member falls below the 60-character LCS threshold:
    `pairEncodeFixed`, whose longest block is 53 characters but whose whole
    91-character source proof reappears. This is why the rule measures
    coverage, not contiguity alone.
- **Pass 2, residual helpers.** Each of the 27 nonmembers recorded in
  round 4 is screened against every public proof of Composition,
  Primitives and TimeConstructible, taking the best match by shared length.
  - Members (2): `f2_strip_linear` (86.0% of `computesFunInTime_stripLast`;
    R5-1) and `f2_counter_heads` (64.1% of `timeConstructible_id`; the
    auditor's 215-character partial-reuse candidate, which crosses the
    member bar once measured by tiling).
  - Fragments, recorded (6): `f2_counter_count_space` 6.5%,
    `f2_unary_sharp` 35.7%, `f2_cond_time` 30.0% (vs
    `bufferedCompTM_computesInTime`, a candidate the auditor did not list),
    `f2_rewind_scan_heads` 7.4%, `f2_rewind_heads` 6.0%,
    `f2_cond_ledger` 11.7%.
  - The remaining 19 share under 60 characters with any public proof.
- **Round-6 repair (R6-1, R6-5): pass 3, exhaustive.** Round 6 found
  R6-1, which the public-only residual pass could not see. Pass 3 replaces
  that scope limit. **Every one of Catalog's 124 non-members** (all of
  Catalog minus the post-R6-1 299-member union, computed by name in the
  script) is screened against **every declaration, public and private, of
  Composition, Primitives, TimeConstructible, Loop and Wrappers** (553
  declarations, of which 542 have an extracted body of at least 25
  characters; the other 11 cannot reach the 60-character floor). An exact 25-character prefilter is used; it loses nothing,
  because every tile is at least 25 characters. Verdicts compare like with
  like, proof with proof and term with term, so a proof that spells out a
  definition's term is reported as a restatement and not counted. **Every**
  qualifying pair is printed, not just each target's best match (R6-5).
  - Result: **19 cross-file members**, all counted in the Catalog row
    above. *Round-7 correction:* the round-6 text derived the source side
    from each target's best match only, giving "6 new source-side members"
    (R7-1). Pass 4 below replaces that hand step.
  - Five A2 members reproduce just over half of one 129-character Loop
    proof, `emLoop_run_prefix`. They are counted, as the rule requires,
    and flagged as low-coverage.
- **Round-7 repair (R7-1, R7-2): pass 4 generates the census.** No
  per-file member count is assembled by hand any more. **Pass 4** runs the
  like-kind rule over **all 423 Catalog declarations**, not only the
  non-members, against all five source files: 537 like-kind MEMBER pairs.
  **Every** pair's source joins its file's member set, together with the
  historical rules, stated by name in the script: f2_-twins, the
  `a2_loop_halted_run` twin, the relocation family, the 13 H3 copies, the
  counter block and `catalog_` twins. The script prints each file's count
  and every member beyond the historical rules, with spans. The rows above
  quote it.
  - Pass 4 reproduces the auditor's R7-1 additions (`controlCfg_run`,
    `emCall_right_run`, `exists_emitLoopTM`).
  - It also finds **24 further source-side members** (Primitives 16, Loop
    7, Wrappers 1). These are source declarations that a Catalog twin of a
    *sibling* declaration reproduces by more than half, so their material
    is duplicated in Catalog. Two of them are Loop's H3 near-copies
    `emLoopHost_init` and `emLoopHost_anchor_return`, previously
    "noted, uncounted"; they are now counted through the cross-file path.
  - Catalog is unchanged at 318.
  - **R7-2:** the body extractor now handles equation-style definitions and
    inductives (text from the first depth-0 `|` or `where`). The population
    labels are exact: 553 source declarations, 542 with an extracted body
    of at least 25 characters; the other 11 are genuinely shorter. Pass 3b
    carries the kind guard: **107 like-kind in-file pairs over 62 targets
    (12 at 90% or more), plus 2 restatements** (`f2_cond_ledger` ~
    `f2_timedReadyCfg`, `a2_loop_prepare` ~ `f2_loopReady`).
- **The membership rule in one sentence.** A declaration is a member when
  it is a historical twin or copy, or when it is either side of a
  like-kind cross-file pair in which at least half of the source's
  extracted body, and at least 60 characters, reappears in the target. The
  **exception** is in-file near-duplicates, which are recorded (pass 3b)
  and not counted; in-file exact copies are counted.
- **Standing in-file convention, stated explicitly.** Pass 3b lists
  in-file near-duplicates among the non-members: **109 raw printed
  pairs, of which 107 are like-kind, over 62 targets**. Twelve like-kind
  pairs reach 90%, and the other 2 are kind-mismatched restatements. They
  are led by the §12 sibling
  machine rows (`transferTM` against `copyTM` 99.8%, and the
  clear/compare/increment rows), which are public constructions audited at
  the §12 and F1 gates. Per the ledger's standing convention, which counts
  in-file **exact** copies (the H3 thirteen, the `a2_mapSumEquiv`/
  `a2_map_sum` pair) and **notes in-file near-duplicates without counting
  them**, they are recorded, not counted. None is an exact copy. Their
  disposition is the 12.2c per-theme split, which factors these families.
  An in-file near-match alone never adds a member. A declaration can still
  be a member independently through a cross-file pair: Loop's
  `emLoopHost_init` and `emLoopHost_anchor_return` count because their
  Catalog twins reproduce them.
- **Coverage qualification.** The screen covers the five source files of
  Catalog's copy families, in full, at the stated thresholds. Copies from
  files outside those families, or adaptations restructured below the
  25-character tile size, are outside it.

Copy-side counts deliberately include copies whose originals were deleted
in R1 (the copies persist; deletion of an original does not shrink the
copy side). The Loop inventory's recorded dispositions — the 8 dead
Loop-twin copies in Catalog (`f2_loop_silent_prefix`,
`f2_loopBody_capture`, the six `f2_loopDebit*`/`f2_loopBorrow*`) and the
orphans' dead twins — are **dispositions for 12.2c, not subtractions
here**; sole-owner/dead labels require Catalog's reference graph and are
settled at that window. Internal near-duplicates flagged by the
inventories but outside the rule (`clCountTape ≡ bufferTape`) are noted,
uncounted. The H3 `_init` pair, once in this list, counts since round 7
through its cross-file Catalog correspondence.

**Epoch R1 delta**: new copies **0**; the historical maps lost **eleven
dead originals plus one live original eliminated by replacement**
(`catalogPair_inverse`, the human-approved E1) — 245 → 233 surviving
→Catalog originals (R2-3 wording); net −1,639 lines, −83 private
declarations (76 dead + 7 replaced).

## Epoch 2, B1 (PR #26): the oracle layer and FH-1

Added at the B1 fill-gate close (`audits/b1-fill-findings.md`, finding 2).
The primary rule applies: each member is counted once per file it
inhabits, and fractions are over the file's total declarations at
`integrate/b1-oracle`. None of these files had a ledger row before.

| File | Total decls | Original-side members | Copy-side members | All members | Fraction | Disposition |
|---|---:|---|---|---:|---:|---|
| `TuringMachine/Oracle.lean` | 42 | 0 | 2: `OracleTM.runFrom_comm_of_step` (63/63 both ways against Deterministic's) and `OracleTM.ComputesInTime.output_unique` (72/87 = 83% of Finite's) | **2** | **4.8%** | Approved forced mirrors (B1 decision 6; gate note 16) |
| `TuringMachine/Deterministic.lean` | 34 | 1: `MultiTapeTM.runFrom_comm_of_step` | 0 | **1** | **2.9%** | Mirror source |
| `TuringMachine/Finite.lean` | 18 | 2: `FinTM.ComputesInTime.output_unique` (mirror source) and `MultiTapeTM.exists_first_halt` (FH-1's public form) | 0 | **2** | **11.1%** | Sources |
| `ClassNP/EXP.lean` | 153 | 0 | 1 (FH-1): `enumCont_first_halt` | **1** | **0.7%** | FH-1, to retire (`backlog.md`) |
| `ClassNP/SAT.lean` | 282 | 0 | 2 (FH-1): `sat_first_halt`, `sat_call_first_halt` | **2** | **0.7%** | FH-1 |
| `CookLevin/Hardness.lean` | 545 | 0 | 1 (FH-1): `clA5_call_first_halt` | **1** (was 0) | **0.2%** | FH-1 |
| `Build/Catalog.lean`, `Build/Loop.lean` | 428, 194 | — | FH-1: `f2_loop_first_halt`, `f2_splitCount_firstHalt` (Catalog); `loop_first_halt` (Loop) | unchanged | — | `loop_first_halt` and `f2_loop_first_halt` are a 341/341 twin pair, already counted in the Loop→Catalog family. `f2_splitCount_firstHalt` is in the F2A-22 inventory; whether it is one of Catalog's 318 members or one of the 20 F2A nonmembers is settled by the FH-1 retirement census |

The FH-1 copies predate the public form. B1 adds no copies, so no file
gains a copy in this epoch and none crosses one fifth.

**Exclusions** (screen hits that are not members, with their dispositions
in `audits/b1-integration.md`, accepted by gate note 17):

- `uw_tail` (Relativization) → E3 `OracleNDTM.stepWith_eq_of_ne_qQuery`
  (OracleNondeterministic), 57%. Glue: shared citations of the
  fixed-choice step bridge.
- `uw_scan_step` → `uw_false_step` (Relativization, in-file), 71%. Glue:
  the shared `uw_step_scan` call line. It is also uncounted under the
  in-file convention.
- `Catalog.f2_loopBody_step` → `queryTM_init` (Classes), 54%. The
  configuration-equality idiom; no machine argument is shared.
- `runFrom_ofMultiTapeTM` → `runFrom_plainEmptyOracle` (Oracle, in-file),
  53%. A screen artifact: both declarations are unchanged (gate note 18).

So Relativization, Classes and OracleNondeterministic have no members.
`OracleNondeterministic`'s private blank-cell bound moved to `Oracle.lean`
as the public `queryString_length_le_of_blank` (C1-P1). Both consumers cite
it, so no copy remains (gate note 8).

## §12.8 statement layer (PR #28)

Added at the §12.8 statement gate, round 1 (`audits/s12-8-statements-findings.md`,
finding 8 and note 38).

- **Catalog's denominator** (2026-10-11). Part 3 adds 31 public declarations,
  none of them members, bringing Catalog to 459 declarations (75 public,
  384 private). The members are unchanged, so the fraction is now
  **318/459 = 69.3%**; strict, 283/459 = 61.7%. The R1-close figure of
  318/428 is the historical snapshot. The scheduled resolution is still the
  12.2c per-theme split.
- **Same-file similarities, not members.** The screen found twelve new pairs,
  all within a file. They are uncounted under the in-file convention:
  - the four seek tables among themselves, including `seekEndTM` ←
    `skipTM` at 100%;
  - `writeConstTM` ← `writeAdvTM` at 58%.

  These are distinct small transition tables over shared phase types, with
  different stop and return behaviour; no proof is copied (gate note 38). The
  fills must use the one shared trace that the sketches promise.
- **The new files** (`SymbolLift`, `Build/Scan`, `Build/InputCall`,
  `Build/CfgRecord`) have no members.

## Wave-1 statements (PR #43): §12.8b, §12.10, §12.11

Added at the wave-1 statement gate, round 2 (`audits/wave1-statements-findings.md`, finding 2;
`audits/wave1-statements-resolutions.md`).

**Round 1's copy-side member is gone.** `CertShell.certificateShell_proj` reproduced
`Nondeterminism`'s private `certificate_split_strictMono` (82/99). By user decision
(2026-10-11) it and both disclosed re-derivations were factored, not acknowledged:

| Mirror (round 1) | Shared home now | Re-derived from it |
|---|---|---|
| certificate split uniqueness and certificate-length monotonicity (`CertShell` against `Nondeterminism`) | `TuringMachine/ChoiceWords.lean`: `append_split_unique`, `certificateLength_strictMono`, `expCertificateLength_strictMono` | `CertShell.certificateShell_proj`, `Nondeterminism`'s split proofs (five privates removed) |
| W2-0, the query-length invariant (`OracleSim` against `Oracle`/`OracleNondeterministic` privates) | `Oracle.lean`: `OracleTM.step_radius`, `OracleTM.runFrom_radius` | W2-0, `Oracle.lean`'s initialized invariant, `runWith_headBlank` |
| the choice-word certificate law (`OracleSim.mem_iff_exists_choiceOut` against `Nondeterminism.choice_certificate_iff`) | `ChoiceWords.lean`: `choiceBudget_le`, `run_take_of_halted` | both laws (`acceptsWithin_iff_of_halts`, `mem_iff_exists_choiceOut`) |

**Members after round 2.** The five statement modules and `ChoiceWords` have no members.
`Nondeterminism`'s count does not grow.

**Exclusions** (screen hits that are not members; for the gate to rule on):
- `Nondeterminism.a3n_unpad_EXP` → `ChoiceWords.expCertificateLength_strictMono`, 82/130
  (63%). A pre-existing in-file pair: the base screen shows it against the former
  `e3_split_strictMono`, also at 63%. It became cross-file when the exponential monotonicity
  moved beside its polynomial sibling. The shared text is one monotone-power inequality
  (`Nat.mul_le_mul_left C (Nat.pow_le_pow_right … (Nat.pow_le_pow_left … c))`) inside an
  unrelated padding proof. No argument is copied.
- `ChoiceWords.certificateLength_strictMono` ↔ `expCertificateLength_strictMono`, 84% / 64%:
  an in-file pair, uncounted under the in-file convention. These are two monotonicity facts
  for two different length functions, NP and NEXP; the pair was in-file in `Nondeterminism`
  before.
- `CodeSimulator.tableBitsK` reproduced by the frozen serializers: `CodeFormat.oneTapeFormat`
  (85%), `CodeFormat.codeTable2Bits` (67%), `Codes2Tape.Code2TM.serialize` (56%),
  `UniversalInterpreter.universalRecords` (56%). This is the **item-8 residual family** (the
  generic writer against the frozen writers, which cannot be redefined), with the bridges
  `tableBitsK_two` and `oneTape_serialize_eq` proving the equalities; gate round 1, note 47.
  The `universalRecords` hit is the same family, visible once round 2 screened the
  `Universal*` files.

## Watch items (design-parallel, no byte-copies)

| Item | Status |
|---|---|
| **ch7 EmitIter layer vs the §12 layer** (merged with PR #11, 2026-10-10): `Build/EmitIterEmbed.lean` exports a **public** tape-padding, state-injecting embedding layer (`padAction`/`embedCfg`/`embed_step`/`embed_run`/`SafeRun` — 18 public declarations, none private; *corrected 2026-10-10: the first version of this row called them private*), written against main (which lacks `Build/Embed.lean`) and structurally parallel to the §12 bank-embedding transformers; the emit-iteration host (`Build/EmitIterBody.lean`, 20 declarations: 1 public, 19 private — corrected at ch7 fill gate round 2, R2-3) parallels the §12/Loop host family. **Body-level screen** (`audits/evidence/ch7/ch7-fill-duplication-screen.md`; the first version of this row rested on a name screen alone): **no copies of pre-existing repository material** — none of the §12 or loop-library material matches; the ch7 modules consume main's public `exists_emitLoopTM`/`exists_emitCallTM`/`exists_installCallTM` rows by citation. This row is design duplication; the stack's own copy family is ledgered below. | **12.2c docket** (user, 2026-10-10): harmonize to one embedding layer and one host family at the per-theme split; the naming of the shared block primitive is settled there too. The ch7 fill gate (`audits/ch7-fill-pack.md`, run on the merged tree; question 7) compares the two layers as facts. Consumption embargo until that gate closes. |
| **Pre-issue shared lemmas for epoch C1** (maintainer, 2026-10-10): `Turing.MultiTapeTM.spaceUsed_le_mul_succ` (`Finite.lean`) is the bound inside Catalog's private `f2_space_of_time`; `Turing.FinTM.toFinNDTM_haltsWithin_and_accepts_iff` (`ClassNP/NTIME.lean`) is `DTIME_subset_NTIME`'s per-input content, which now cites it; `Complexity.SPACE.mono_const` and `Turing.FinTM.computesInSpace_zero_of_k_eq_zero` (`SpaceComplexity/Basic.lean`). They were landed so that C1a/C1b cite instead of copying. **Residual:** `f2_space_of_time` should become a citation of the public bound in 12.2c T3 (Catalog core). Also recorded for later tranches (item 11 dossier): private live-prefix copies of `runFrom_state_ne_none_of_le` in Catalog, Hardness and SAT, and Loop's `loop_input_run_le`, which equals the public `timed_input_bound` (removed in 11A) | Watch; T3 / T2 |

## Acknowledgment and disposition state

| Debt family | Acknowledgment | Cleanup owner and window |
|---|---|---|
| Catalog's 318 expanded members (↔ Primitives/Loop/Wrappers/Composition/TimeConstructible + in-file) | **D-R2** (user, 2026-10-09) | the **12.2c** per-theme refactor, promoted to the next window after R1; precondition (shrunken `Build/` files) met |
| **The §12 sibling rows' in-file repetition** (`transferTM`/`copyTM`/`clearTM`/`compareTM`/`incrementTM`, their traces, framed contracts, canonical rows and space rows; pass 3b and the copy-text screen). **Grown by the §12.6 fill:** 16 new directed pairs (5,520 matched characters), against 20 gone and a net −330 characters (`audits/evidence/s12-framed-fill/copytext-diff.txt`). Examples: transfer-framed → copy-framed 97%, and increment success → overflow 90% | **12.2c item 5** on the user-consolidated tasklist (2026-10-10). The §12.6 fill gate ruled the growth inside this acknowledged family, so a minor (`audits/s12-framed-fill-findings.md` F1/F2) | the user's **12.2c**, item 5: a common scanner. Its scope now explicitly includes the generalized traces, the framed consequence proofs, the canonical specializations and the space wrappers |
| Loop's 13 H3 copies (+1 near-copy) | **D-R3** (user, 2026-10-09) commissioned the collapse mechanism — §13 Z5, **now proved** (vhost-f1) | **ACKNOWLEDGED (user, 2026-10-09): retrofit batch RB4** (Loop), consuming Z5, window: after the A-S1 fill gate closes — **RB4 merged (PR #13, 2026-10-10): 12 of 13 H3 copies deleted by Z5 transfer; `emLoopHost_prepare` survives with a rewritten proof, still counted.** The inlined residue is the row "RB4's inlined residue in Loop" below |
| The three-file relocation family (4 decls × 3 files; pre-policy legacy, disclosed at its batches as "private harvest" but verbatim in fact) | **the user, 2026-10-09** (the round-2 audit's R2-2 disposition) | **ACKNOWLEDGED (user, 2026-10-09): the same RB4** (all three files), replacing the family with the R1 selected-tape exports (D-R1, proved) + Z5 agreement transfer, per the inventories' own analysis of what unlocks it — **RB4 (2026-10-10): Loop's 4 originals DELETED** (R1 embedding + injective state transport + Z5). **Primitives' and Hardness's 4 + 4 copies REMAIN.** Their generic interfaces are stronger than R1 (aliased host slots, non-injective state maps), so a literal replacement would weaken surviving statements. Continuation: **RB5 (revision 2, 2026-10-10)** promotes `runFrom_mapState_of_agreeOn` into `Build/Embed.lean` (it needs both `StateRenaming` and Z5, and only Embed already imports both), then specializes per concrete layout, Primitives before Hardness. **DISCHARGED (RB5, PR #14, merged by the user 2026-10-10):** all 12 family members are gone. Primitives' and Hardness's copies are deleted, and every relocation pair is gone from the copy-text screen (739 → 692 pairs over the four files, with no new pair). The census twin `f2_splitEmbed_run` in Catalog survives; it is now a special case of the public lemma, and 12.2c item 2 can replace it by a citation |
| **RB4's inlined residue in Loop** (post-merge copy-text finding, 2026-10-10): the forwarding host's consumers reproduce the original loop host's phase proofs. `emLoopHost_round` reproduces 100% of `loopHost_reject`; `emLoopHost_prepare` 99% of `loopHost_prepare` and 100% of `loopHost_input_rewind`; `emLoopHost_anchor_return` 95%; `emLoopHost_start` 92%. The frame pairs `emCall_bank_*` (94%) and `emCall_finish_*` (79%) grew more alike. In all, 11,476 characters of the forwarding host reproduce the original (`audits/evidence/retrofit/copy-text-screen.py`) | **ACKNOWLEDGED (user, 2026-10-10)**: RB4 accepted as merged, and RB5's Loop task withdrawn. The residue is not removable phase by phase: the `loopHost_*` lemmas state endpoints only, and the anchor-return phase runs in body control from `t = 0`, exactly where the two hosts differ (RB5's first dispatch kernel-checked the counterexample) | the user's **12.2c**, tasklist item 11: unify the two hosts structurally |
| **ch7 block stack's per-loop lemma family** (PR #11, 2026-10-10): the OR/XOR/majority loops re-prove one orbit/length/init/emit lemma set under renaming. **Census corrected at ch7 fill gate round 2 (R2-2) to the standing source-inclusive rule, as lower bounds:** `PolyTimeBlockTests` **≥ 12/25 (48%)**, `PolyTimeBlockMajority` **≥ 8/14 (57%)**, `PolyTimeBlockLoop` ≥ 1/32. The first record (4/14 and 2/25) counted copy sides only, and the round-2 auditor found four more cross-file adaptations, `anyStep`/`majStep`, `anyEmit`/`majEmit`, the orbit lemmas and the loop outputs (81–93%), plus two length correspondences (`audits/ch7-fill-r2-findings.md`). The pre-screen is `audits/evidence/ch7/ch7-fill-duplication-screen.md`, whose method description is corrected | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D1**, opened under the one-fifth rule and answered. **Extension ACKNOWLEDGED (user, 2026-10-10, round 2)**: the enlarged family and the `PolyTimeBlockTests` threshold crossing | the **12.2c** per-theme refactor (the user's own window; colleagues spared deduplication work): one generic lemma set in `PolyTimeBlockLoop`, statements unchanged, coordinated with the ch7 owner, after the ch7 fill gate closes **DISCHARGED 2026-10-11** (12.2c T1 item 7, PR #18; gate CLOSED round 1, 0/0/3 minors swept): the generic layer `Complexity.BlockLoop`; census Tests 22/25 → 0/8, Majority 12/14 → 0/6, Loop 6/32 → 0/50; six-file screen 125 / 47,734 → 41 / 10,045. Residual: the excluded `length_xorPairStep_le`/`length_sliceDropAt_le` near-copy (watch). |
| **ch7 `EmitIterEmbed` run-infrastructure re-proofs** (ch7 fill gate round 2, R2-1): five facts are re-proved rather than cited, so **≥ 5/18 = 27.8%, over one fifth**. They are `step_output_prefix` and `runFrom_output_prefix` (Loop's private `emLoop_step_prefix`/`emLoop_run_prefix`), `runFrom_output_extends` (a specialization of `Finite`'s public `MultiTapeTM.output_prefix`), `runFrom_of_halted` (`Deterministic`'s public `runFrom_of_halt`), and `state_isSome_of_runFrom` (Loop's private `loop_live_prefix`). The screen missed all five because the proofs were restructured | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH7-D2** | the user's **12.2c**, item 6: one shared home for the run facts (output-prefix commutation and extension, halting absorption, live prefix) in `Deterministic.lean`/`Finite.lean`, beside `runFrom_of_halt`. `EmitIterEmbed`'s five become citations or re-exports, statements unchanged, and Loop's three private copies are deleted. Coordinated with the ch7 owner |
| **`Codes2Tape.lean`'s format-specific parse layer** (ZF-B/B2, 2026-10-10): 23/33 two-tape instances of `CodeParser.lean`'s one-tape top layer (69.7%; 3 strict) | **ACKNOWLEDGED (user, 2026-10-10)** — `backlog.md` §1 **CH34-D2** | the **12.2c** tasklist item 8: a format-parameterized parse layer (one-tape, two-tape, ND), statements unchanged. **DISCHARGED 2026-10-11** (PR #19, gate CLOSED round 1, 0/0/0): adaptations 23 → 1 (`zfBFallback`, approved residual); screen 117 / 29,824 → 77 / 12,563; all 44 CodeParser/Codes2Tape and 7 Codes2Tape/MathlibBridge pairs gone. Brief `briefs/ch34-t1-item8.md` (tranche T1); the generic layer's resemblance to the frozen one-tape definitions it bridges (`actionBitsK`↔`actionBits`, `codeSkipActionK`↔`codeSkipAction`, the table writer against the three frozen `serialize` bodies) is pre-named in the brief and stays as a residual watch item |

**R8.0b E1, the mandated `counterLoopTMVia`/`counterLoopTM` definition pair** (§12.8 stream D,
PR #38): `CounterLoop.counterLoopTMVia` reproduces 261/287 = 91% of the frozen
`counterLoopTM`, and 84% the other way. It is a definition pair that the R8.0b brief itself
mandated; there is no copied proof. **ACKNOWLEDGED (user, 2026-10-11)**, as a one-off exception
for exactly this pair (R8.0b gate finding F1). **Cleanup owner and window:** the maintainer, in
**12.2c**, through backlog §1 R80B-E1: redefine `counterLoopTM` as the identity-embedding
instance and re-check consumers. `CounterLoop`'s other new pair, `counterLoopTM_run_done`
↔ `_run_escape` at 83%/72%, is two Z5 re-derivations sharing transport setup. It is not a
member (gate note F8).

**RW-1, the rewind row's copies of Catalog's seek frame and skip-back table** (PR #138,
`Build/Rewind`, 2026-10-18). Two like-kind cross-file pairs, both against `Build/Catalog`:
- the private `rw_cfg` reproduces Catalog's private `catalogSeekCfg` at 79/79 = 100%, both ways:
  one record update over a different phase type; no proof is copied;
- `rewindTM` and `skipBackTM` share one contiguous 140-character block, 80% of `rewindTM`'s
  175-character body and 69% of `skipBackTM`'s 202: `rewindTM`'s table is `skipBackTM`'s
  without its first row, with `start` in the role of `gap`. Inside the same 140 characters,
  `rewindTM` also pairs with the seek tables `seekStartTM` (98 characters, 56% of `rewindTM`),
  `skipTM` (71, 55% of `skipTM`) and `seekEndTM` (92, 53% of `rewindTM`): the seek family's
  table pattern.

**Census** (the primary rule, each member counted once per file it inhabits; corrected at gate
55, finding 1: the first version counted `rw_cfg` alone, 1 of 5, and called the table pairs
design-parallel, an exception the rule does not make for cross-file pairs; the seek tables'
resemblance among themselves, §12.8 statement layer above, is uncounted only because it is
in-file):
- `Build/Rewind`, the copy side: **2 of 5 declarations (40%)** (3 public, 2 private), **20**
  lines in member blocks (`rewindTM` 14, `rw_cfg` 6), 219 characters reproduced. `RewindPhase`
  (a 48-character body, below the floor) and `rw_step` (no pair at half) are not members.
- `Build/Catalog`, the original side: **5 more members**, `catalogSeekCfg` (6 lines),
  `skipBackTM` (16), `skipTM` (13), `seekEndTM` (18) and `seekStartTM` (19), 72 lines; 5 of its
  505 declarations. The file's row is re-totalled at its next census.
- The v3 screen of the module, `Build/Catalog` and the exhaustive replay at #136's head (563
  declarations, 416 pairs) regenerates byte-identical at gate 55; screened against the whole
  library, `rewindTM` and `rw_cfg` pair with nothing else.

**Exclusion** (a screen hit that is not a member; an exception to the rule, approved by the user
on 2026-10-21): `rewindTM_run_ofCfg` → Catalog's private `a2_mapSetup_run`, 84/163 = 52%. The shared
text is two tiles, 50 and 34 characters, of the run-by-induction idiom
(`| succ t ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih (` and
`, MultiTapeTM.runFrom_succ_eq_step'`); no setup argument is shared. Screened against the whole
library, the same idiom reaches half of 12 short run proofs in 10 files: `a2_mapSetup_run`,
`Universal`'s `timedFrame_run`, `Robustness/ObliviousSchedule`'s `maskedClock_lockstep`,
`decorateTM_run` and `parallelTM_run`, `Nondeterminism`'s `b2_unary_run`, `CircuitEvalRun`'s
`step_rej`, `Build/Seam`'s `seamCompTM_runFrom_left`, `TimeHierarchy/ClockMachine`'s
`kCfg_run`, `SymbolLift`'s `MultiTapeTM.liftSymbols_runFrom`, `Composition`'s
`controlCfg_run`, and `Build/NDHost`'s `wr_cfg_scan` (there the frame-read idiom). As with the
B1 exclusion of the configuration-equality idiom (above), it is recorded, not counted. Counted,
`Build/Rewind` would be 3/5 = 60%.

**The one-fifth rule** (`workflow.md` §4): `Build/Rewind` is past one fifth. Its §1 item is
`backlog.md` RW-1, opened and acknowledged on 2026-10-18, before gate 55's pack shipped, for the
frame alone; gate 55 widens it to the table. `Build/Catalog` was past one fifth already (D-R2).

**Acknowledgment.** The frame: **ACKNOWLEDGED (user, 2026-10-18)**, before gate 55. The table
and the exclusion: **ACKNOWLEDGED (user, 2026-10-21)** (gate 55, finding 1: the census at 40%,
the idiom hit excluded), with the retirement by unification below chosen over a frame-only one. **Cleanup owner
and window:** the user's dedup window, through backlog §1 RW-1, with Catalog's next edit: one
public frame over any state type, cited from both files; and one left-pass table, the rewind
being skip back entered at `gap`, with both framed runs derived from one public back-pass run.
After the retirement, neither file has a member from this family.

**BW-1, the buffer-word identities** (PR #140, `TuringMachine/BufferWords`, 2026-10-18): four of the
module's six public lemmas restate `Build/StepBlock`'s privates (`bufferTape_append_shift` ↔
`bufferTape_suffix`, `bufferTape_append_mid` ↔ `bufferTape_reads`, `bufferTape_eq_none_of_not_mem`
↔ `bufferTape_outside`, `bufferTape_unary` ↔ `bufferTape_unary`): the same statements, with
different proofs (the new ones read `bufferTape` only through its published equations). The
copy-text screen pairs none of them, so this is a restated-fact family, not a text copy.
**ACKNOWLEDGED (user, 2026-10-18)**, in the ruling that chose the public module. **Cleanup owner
and window:** the user's dedup window: `StepBlock` imports the module and its four privates are
deleted, their uses re-pointed. **Census** (the primary rule, each member counted once per file it
inhabits; corrected at gate 57, finding 1: the first version counted `StepBlock`'s side only,
without fractions or spans):
- `TuringMachine/BufferWords`, the original side: **4 of 6 declarations (66.7%)** (6 public,
  0 private; `_drop` and `_take` have no counterpart), **45** lines in member blocks
  (`_append_shift` 10, `_append_mid` 9, `_eq_none_of_not_mem` 10, `_unary` 16).
- `Build/StepBlock`, the copy side: **4 of 135 declarations (3.0%)** (64 public, 71 private),
  **42** lines (`bufferTape_unary` 11, `_outside` 7, `_reads` 16, `_suffix` 8).
- No copied characters: the v3 screen of the module, `Simulation`, `Build/StepBlock` and
  `Build/SeamLayout` (140 declarations, 32 pairs) pairs none of the eight, before and after
  #140's merge of the campaign branch (`7c963897`).

**The one-fifth rule** (`workflow.md` §4): `BufferWords` is past one fifth, and its §1 item is
`backlog.md` BW-1, opened and acknowledged on 2026-10-18, before gate 57's pack shipped.
`StepBlock` is under one fifth, and #140 leaves it byte-unchanged. After the retirement, neither
file has a member.

**IW-1, the window copier's interval patch** (PR #137, `Build/InputWindow`, 2026-10-21): the
private `iw_patch` is `Build/StepClock`'s public `wordPatch` at `Γ = Bool`: token for token after
renaming its binders (`tape`, `head`, `v` for `ct`, `cp`, `u`), and equal by `rfl`
(`@iw_patch = @wordPatch Bool`). One definition; no proof is copied. The same definition is also
`Build/CounterLoop`'s private `counterPatch` and `Build/Catalog`'s private `catalogTape` (written
pointwise), both from 2026-10-10; `wordPatch` (2026-10-14) is the public one. These four are the
**interval-patch family**: the tree and the open branches hold no other. The B6 F1 record named
`counterPatch` for the dedup window; `catalogTape` was not recorded before. The worker reported
"new copies: none" (`StepClock` was outside its screen population and its import context). The
maintainer disclosed the copy in gate 54's pack (question 6), and gate 54's finding 1 made it a
debt major. **Not members:** `iw_patch_append` appends one cell (Catalog's public
`catalog_write_take` states the same fact in take form, with its own proof), and `iw_patch_true`
reads the patch at the all-true word (the `Bool` case of a step inside `CounterLoop`'s proof, not
a declaration). **ACKNOWLEDGED (user, 2026-10-21)**, at gate 54, for the whole family. **Cleanup
owner and window:** the user's dedup window, through backlog §1 IW-1: `wordPatch` moves below
`Build/Catalog` with Catalog's next edit, and the three private copies re-point to it
(`InputWindow`'s re-proofs are verified at gate 54's review). **Census** (the primary rule, each
member counted once per file it inhabits; declarations as the style lint counts them; lines by
the span rule):
- `Build/InputWindow`, a copy: **1 of 17 declarations (5.9%)** (1 public, 16 private), **5**
  lines (`iw_patch`).
- `Build/StepClock`, the public one: **1 of 41 (2.4%)** (8 public, 33 private), **4** lines
  (`wordPatch`). From #139 on, **1 of 42 (2.4%)** (9 public): #139 adds `wordPatch_append`, a
  member of WA-1 below.
- `Build/CounterLoop`: **1 of 79 (1.3%)** (59 public, 20 private), **4** lines (`counterPatch`).
- `Build/Catalog`: **1 of 505 (0.2%)** (113 public, 392 private), **5** lines (`catalogTape`). It
  is in none of the correspondences behind Catalog's row above, so it adds one member there.
- Copied characters: none by the v3 screen, which pairs none of the four. After renaming, each
  is the same definition of 175 to 199 characters.

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.
`InputWindow` had no earlier copies. `Catalog` had, but #137 adds no copy to it, since
`catalogTape` predates the delivery. The §1 item IW-1 is opened anyway, as for RW-1, and
answered. After the retirement only `wordPatch` remains, in its new home.

**WA-1, the adjacent-patch law** (PR #139, `Build/StepClock`, 2026-10-18; ledgered at gate 56,
finding 2): the public `wordPatch_append`,
`wordPatch (wordPatch ct cp u) (cp + u.length) v = wordPatch ct cp (u ++ v)`, restates
`Build/RecordTable`'s private `rt_adjacentWrites` (2026-10-13). With `wordPatch` unfolded and
beta-reduced, the two elaborated statements are alpha-equivalent: they differ only in binder
names (`tape`, `o` for `ct`, `cp`), checked on the compiled declarations at #139's merged head
(gate 56's review). The proofs differ (the new one reads `wordPatch` and `FinTM.bufferTape` only
through their published equations; `rt_adjacentWrites` unfolds `FinTM.bufferTape`), and the v3
screen pairs neither, so this is a restated-fact family, not a text copy, as BW-1 is. The F3 review
that proposed the lemma disclosed the pair, and the ruling that chose it named it (backlog §2, F3
cont1: "E2 ruled (user, 2026-10-18): B"), but it was not ledgered until gate 56.
**Acknowledgment:** the ruling of 2026-10-18 that chose option B (F3's E2). The decision put to
the user named the re-point ("which also opens the `rt_adjacentWrites` re-point"), and the
ruling's record names `rt_adjacentWrites` as the lemma's private form, to re-point in the user's
dedup window. The record does not call the pair a copy family, as the same day's BW-1 ruling
does; gate 56's review (finding 2) reads the ruling as acknowledging it. **Confirmed (user,
2026-10-22):** the ruling acknowledges the pair. **Cleanup owner and window:**
the user's dedup window, through backlog §1 WA-1, with IW-1's move: once `wordPatch`, its cell
lemmas, `wordPatch_append` and the explicit-form lemma are below `Build/Catalog`, they are in
`RecordTable`'s closure; `rt_adjacentWrites` is deleted, and its one use (`rt_advanceCfg_append`)
cites `wordPatch_append`. **Census** (the primary rule, each member counted once per file it
inhabits; declarations as the style lint counts them at #139's merged head `1cd66f1b`; lines by
the span rule):
- `Build/StepClock`, the public one: **1 of 42 declarations (2.4%)** (9 public, 33 private),
  **25** lines (`wordPatch_append`). With IW-1's `wordPatch` (4 lines), the file has **2 members
  of 42 (4.8%)**, **29** lines.
- `Build/RecordTable`, the private one: **1 of 129 (0.8%)** (29 public, 100 private), **28** lines
  (`rt_adjacentWrites`). It had no member before.
- Copied characters: none. The v3 screen of `StepClock`, `RecordTable`, `WindowClock` and
  `WindowRun` (176 declarations, 19 pairs) pairs neither.

**The one-fifth rule** (`workflow.md` §4): neither file is past one fifth. #139 adds no copy to a
file that received copies before: `StepClock`'s earlier member is IW-1's `wordPatch`, the public
original, and #139 leaves `RecordTable` byte-unchanged. The §1 item WA-1 is opened anyway, as for
RW-1 and IW-1, and answered. After the retirement only `wordPatch_append` remains, in
`wordPatch`'s new home.

**C1-E cont1, the exhaustive replay** (PR #136, `ClassNP/ExhaustiveReplay`, 2026-10-21): **no
member.** The v3 screen's 122 new pairs are all in-file (0 cross-file, 0 gone; 297 → 428
declarations, 106 → 228 pairs). 26 are at or above the brief's 90% copy threshold, between 17 of
the module's 185 declarations (9.2%): the twenty `xr_*_ne_*` one-liners, two pairs of leaf tables,
two buffer-tape facts and the replay's two exits. They are disclosed in-file siblings, listed and
justified by family in the worker's report (§8) and qualified by its erratum
(`campaign/fills/c1/reports/exhaustive-2-ERRATUM.md`); gate 53 (minor 2, note 12) found no copied
material needing acknowledgment. Their consolidation, and the re-points to the public lemmas that
arrived after the fill's base, are `backlog.md` §1 C1E-1, in the user's dedup window.

**IR-1, the input rewind family** (megafill A, 2026-10-22). Four private input rewinds, each
with its own exact-time run proof:
- `ClassNP/ExhaustiveReplay`'s `xr_inRewindTM` (#136) and UN cont1's `un_inRewTM`
  (`Diagonalization/NTimeHierarchy`, 61% and 59% on the v3 screen): a cross-file pair, which the
  UN brief forbids;
- U2-S cont1's `ss_inputRewind` (`UniversalK`, #147);
- R cont2's `ic_rewind_scan` (`TuringMachine/NDCodeSimulator`), which re-proves the public
  `Turing.FinTM.rewind_scan` (51%; `Simulation` was outside that brief's screen population, so the
  worker's screen could not see it).

With them, UN's `un_mapState_comp` shares field-equation proof text with `ExhaustiveReplay`'s
`xr_E_initCfg` (54%; their statements differ: gate 65, minor 3).
**Acknowledgment and disposition (user, 2026-10-22):** UN's two pairs are resolved by **an API PR
first**: a public input rewind with an exact time and a first-visit cut, and a `mapState`
collapse lemma. UN's landing re-points to them. R's copy lands ledgered and re-points when that
API lands. U2-S's and `ExhaustiveReplay`'s are re-pointed in the user's dedup window.
**The API: #153** (2026-10-22): `Build/InputRewind`'s `Turing.inputRewindTM` and
`inputRewindTM_run`, and `Turing.Cfg.mapState_mapState`. Its v3 screen pairs the machine with
`xr_inRewindTM` (82% and 73%), and the lemma's proof text with `xr_E_initCfg`'s (54%; a shared
idiom, not a restatement: the composition lemma alone does not replace `xr_E_initCfg`); both are
in the dedup window, as above.
**Retirements (2026-10-23):** NDHost's `guessRun_mapState_mapState` with #153; R's
`ic_rewindLeafTM`, `ic_rewind_scan` and `ic_rewind_leaf_run` with #151; the canonizer's
`canonGramMapComp` with #152; UN's `un_inRewTM`, `un_inRew_run` and `un_mapState_comp` with #154
(its landing). Remaining in IR-1: `ExhaustiveReplay`'s `xr_inRewindTM` and `xr_E_initCfg` and U2-S's
`ss_inputRewind` (`UniversalK`), in the user's dedup window. A fifth copy found while building it, `Build/NDHost`'s private
`guessRun_mapState_mapState` (the lemma's exact statement), is removed in #153 (the user's ruling).
A sixth, found 2026-10-23 on #152's branch: the canonizer's private `canonGramMapComp`
(`TuringMachine/CodeSimulator`), the lemma's statement with the composite as `fun s => g (f s)`,
used at two `rw` sites; 99% each way on the v3 screen. **Disposition (user, 2026-10-23): re-pointed
at #152's landing** (prepared locally, `local/canon-mapcomp-repoint`), as for R's leaf.

**CC7-1, the canonizer cont7's in-file families** (megafill A item 3, `TuringMachine/CodeSimulator`,
2026-10-22). 59 new in-file pairs, none cross-file. Four are at or above 90%:
`canonGramCut_leg`/`canonStageCut_leg` (97% each way), `canonStageLeg4` → `canonStageLeg1` (94%)
and `canonStageLeg5` → `canonStageLeg1` (91%). Three families: the cut leg, the leg template and
the per-record bound. **Acknowledged (user, 2026-10-22): recorded as debt**, for the user's dedup
window, together with the retirement of the now-unused `canonCounterRepeat` link (the user,
2026-10-22).
**Census** (gate 67, minor 3; the primary rule, each member counted once per file it inhabits;
declarations as the style lint counts them; lines by the span rule, at #152's head `aed162fd`):
- the members, by family (11):
  - the cut leg (2): `canonGramCut_leg` (lines 7564–7585, 22), `canonStageCut_leg` (6332–6352,
    21);
  - the leg template (7): `canonStageLeg0`–`canonStageLeg6` (6354–7046: 90, 86, 91, 109, 106,
    98 and 107 lines);
  - the per-record bound (2): `canonStageBlock_consumes` (5669–5687, 19) and the base's frozen
    private `skipTable_consumes` (233–245, 13), whose local per-record bound it re-proves (61%);
- with IR-1's `canonGramMapComp` (7595–7607, 13), a cross-file member until #152's landing
  re-points it.

`TuringMachine/CodeSimulator`: **12 of 198 declarations (6.1%)** at the head (12 public, 186
private), **775** lines in member blocks; after the re-point, **11 of 197 (5.6%)**, **762** lines.
The file had no earlier ledger member: the item-8 entry's `tableBitsK` now lives in
`Build/StepBlock`. The review's other new in-file pairs, those not between two members of these
families, are screen matches, not members: all below 90%, between declarations with different
statements. **The one-fifth rule** (`workflow.md` §4): not reached.

**SD-1, the suffix drop** (PR #161, U2's API, 2026-10-24). One fact,
`(pairEncode u x).drop (2 * u.length + 2) = x`, in four files:
- `Turing.pairEncode_drop` (public, `Build/InputDevice`, line 198, new in #161), the one U2 cites;
- `NDCodeSimulator`'s private `ic_input_suffix` (line 340): the same statement and proof, 100% each
  way on the v3 screen (#161's evidence). **Retired** (2026-10-25): #162 moved it into
  `Build/InterpreterStartup` as the private `is_input_suffix`, and gate 74's round 2 deleted it
  there, the window call citing `Turing.pairEncode_drop` (the kit imports `Build/InputDevice`);
- `Complexity.Codec.pe_drop` (public, `SpaceComplexity/Codec/Parse`, line 69) and `PathWalk`'s
  private `drop_pairEncode` (line 225): the same statement through `pairEncode_eq_dbl`, different
  proofs (no screen pair).

*Historical (at #161's opening):* none of the four files could cite another's without a new import
(`InputDevice` was upstream of none of `NDCodeSimulator`, `Codec/Parse`, `PathWalk`). **Acknowledged
(user, 2026-10-24)**: the U2 review's F2 recommendation (publish `pairEncode_drop` with the API PR,
ledger the family) was the ruling's content. **Disposition:** the startup-kit re-point is **done**
(gate 74's round 2): the kit imports `Build/InputDevice`, so `NDCodeSimulator` sees it through the
kit, and the window call cites `Turing.pairEncode_drop`. Only the `Codec/Parse` and `PathWalk`
members remain, for the user's dedup window: one home beside `pairEncode_eq` in `Encoding` (a large
replay, hence the window). **Census** (one member per file): `InputDevice` 1 of 57 declarations
(1.8%), `Codec/Parse` 1 of 16 (6.3%), `PathWalk` 1 of 32 (3.1%); `NDCodeSimulator` and
`Build/InterpreterStartup` 0 since gate 74's round 2. The one-fifth rule is not reached.

**SK-1, U2-S's capture start** (PR #162, the startup-kit API PR, 2026-10-24). The kit's public
`Turing.embedSilentCfg_initCfg` (`Build/InterpreterStartup`) is U2-S's private
`ss_captureInitial` (`UniversalK`, line 329), harvested verbatim: 100% each way on the v3 screen.
`UniversalK` cannot cite the kit until `CodeSimulator` imports it (B5a's landing). U2-S's other
`ss_` startup pieces are the kit's constructions under other contracts (no screen pair). **By the
ruling (2026-10-24, the B5a review's recommendation)** they go to the user's dedup window, or to
U2's fill once `UniversalK` sees the kit. **Census** (gate 74, major 1, corrected at its round 2):
`Build/InterpreterStartup` 1 of 8 declarations (12.5%), the public `embedSilentCfg_initCfg`, 40
lines with its docstring; `UniversalK` 1 of 51 (2.0%), the private `ss_captureInitial`, 39 lines.
Round 1's kit had a second member, SD-1's suffix drop (2 of 9, 22.2%, past the one-fifth rule);
round 2 deleted it (SD-1 above), so the rule is not reached.

**RI-1, the round iteration along a sequence** (§13d G4 continuation 4, its review's F2,
2026-10-25). `Build/ZoneRebalance`'s private `zr_pinLoop` (line 8266, 71 lines with its docstring)
iterates pinned rounds by its own induction (`Round.segment`, then `Segment.trans`), which is the
proof of the published `Turing.Round.iterate` (`Build/Contract/Basic`, line 781), along the sequence
of pass indices `nxt^[m] j₀` instead of the configuration orbit `roundOrbit`. No published lemma
states the sequence form, so it re-derives `Round.iterate`'s argument, not its statement (the text
screen pairs nothing). All seven of the found path's passes go through it (`zr_passContract`). **The
ruling (user, 2026-10-25): land G4 with this entry; then an API PR adds the sequence form to
`Build/Contract/Basic`, with `Round.iterate` as its corollary, and re-points `zr_pinLoop` to it.**
Census (one member per file; the source side added at gate 75's minor 5): `Build/ZoneRebalance` 1 of
871 declarations (0.1%), the private `zr_pinLoop`, 71 lines with its docstring;
`Build/Contract/Basic` 1 of 85 (84 public, 1 private; 1.2%), the public `Turing.Round.iterate`, 18
lines with its docstring. The one-fifth rule is not reached. **The API PR is #167** (gate 78,
2026-10-25; stacked on #165): `Turing.Round.iterate_seq` beside `Round.iterate`, which becomes its
corollary, and `zr_pinLoop` re-pointed to it. On its landing RI-1 is retired. **Retired
(2026-10-26):** #167 merged as `4c8c2e7e`; `zr_pinLoop` cites `Round.iterate_seq`.

**SG-1, segment concatenation over a private segment predicate** (gate 98's finding 1,
2026-11-06). Two private predicates restate `Turing.Segment` (`Build/Contract/Basic`) at fixed
parameters, and each has its own concatenation lemma re-proving `Segment.trans`:
- `ClassNP/Tautology`'s `tautDualSegment c d t` is `Segment tautDualTM.tm {some .anchor}
  (fun _ => True) c d t`; `tautDual_segment_add` repeats `Segment.trans`'s endpoint and
  forbidden-prefix argument (the v3 screen pairs it with `Segment.trans`, 91/168, 54%);
- `Build/CounterLoop`'s `counterSpan` is a segment from `z` to its run endpoint over
  `{some .done, some .escape}`, whose head relation combines the counter head's interval and the
  body heads' `R`; `counter_span_append` repeats `Segment.trans`, then `Segment.mono` for the
  two relations.

Both predate #202 (the API PR whose gate found them); #202 adds no member. **ACKNOWLEDGED by kind
(the user, 2026-11-06):** every private predicate that restates `Turing.Segment` at fixed
parameters, with its concatenation lemma. **Cleanup owner and window:** the maintainer, in the
dedup window (12.2c): a bridge `tautDualSegment c d t ↔ Segment …` (and the same for
`counterSpan`), then `Segment.trans`/`Segment.mono` through it, deleting both concatenation
lemmas. **Census** (gate 98's, each member counted once per file; the source side included):
- `Build/Contract/Basic`, the public source: **1 of 93 (1.1%)**, `Segment.trans`, 20 lines;
- `ClassNP/Tautology`: **1 of 93 (1.1%)**, `tautDual_segment_add`, 12 lines. The file has no other
  recorded member;
- `Build/CounterLoop`: **1 of 79 (1.3%)**, `counter_span_append`, 28 lines. The file's
  recorded total, every acknowledged member counted once (corrected at gate 98's round-2 minor
  1): SG-1's `counter_span_append`, IW-1's `counterPatch` and R8.0b E1's pair `counterLoopTM`/
  `counterLoopTMVia`, **4 of 79 (5.1%)**, 68 lines (28 + 4 + 19 + 17).

**The one-fifth rule** (`workflow.md` §4): no file of the family is past one fifth.

**BL-2, the binary width of an incremented register value** (gate 101's finding 1,
2026-11-06). The bound `m ≤ 2 ^ e + 1 → |Nat.bits (m + 1)| ≤ e + 2`, through
`m + 1 < 4 · 2 ^ e = 2 ^ (e + 2)` and BL-1 (i)'s `length_bits_le`, was proved three times:
- `Logspace/ISCountGenCorrect`'s private `bits_succ_le` (BL-1 (i) lists it as a site that cites
  `length_bits_le`; its successor/exponential step is this family's);
- `Machines/ARMWidth`'s `arm_decides_pspace_val`, an inline `hlt` block at `N = C₀ (|x| + 1)^c₀`;
- `SavitchARM/Deepen`'s `deepen_contract` (new in #208), the same block at `W · W`.

Census (gate 101's, one member in each file): `Deepen` 1 of 45, `ARMWidth` 1 of 5,
`ISCountGenCorrect` 1 of 9. No file is past one fifth (`ARMWidth`'s 1 of 5 is at it).
**Ruled (the user, 2026-11-06): harvest in #208, all three.** `#208`'s commit `9db4f2ee`
publishes `Complexity.LogProg.length_bits_succ_le` in `Machines/Bin`, beside `length_bits_le`;
`bits_succ_le` is deleted, and the two inline blocks cite it. A library search for the
`4 · 2 ^ e` step (`2 ^ (… + 2) = 4 * 2 ^ …`) finds no other member: `ExpBFS/Main:535–539`
bounds a `Nat.log` width and a memory range, and `BinaryArith/AddSub:174` a sum of two words, both
other statements. **Retired on #208's merge.**

**IL-1, the input-length decider's answer** (gate 101's round-2 screen, 2026-11-06). The
public `Complexity.indicator_inputLenLang` (`Logspace/InputAccess`, since the ARM dedup `56716442`)
states that `inputLenLang` answers `decide (a < |y|)` on `pairEncode y (bits a)`. Six proofs
unfolded their decider table and repeated its two-line proof
(`inputLenLang`, `indicator_indexLang_pairEncode`, `decide_eq_decide.mpr Iff.rfl`):
- `Logspace/ISCountGenCorrect`'s `gen_start` (`hq`), which the v3 screen pairs with
  `indicator_inputLenLang` and with `ExpBFS/Main`'s `orcN_len` at 94%;
- `ExpBFS/Main`'s `orcN_len`, `SavitchARM/Correct`'s `hq`, `Machines/ARMWidthExample`'s `hq`,
  `Logspace/PathHardRegs`' `orc_len` and `Randomized/SpaceAmplifyPoly`'s input-length loop (each
  under the screen's cut-off or outside its population; found by `git grep` for the closing step).

All six predate #208; `Deepen` cites the lemma. Census: one member in each file. No file is past
one fifth. **Ruled (the user, 2026-11-06): re-point all six in #208.** #208's commit `6a289c50`
replaces each by the table's unfolding and `indicator_inputLenLang`; each file elaborates.

**Widened by kind (2026-11-06):** every proof that re-derives one of `InputAccess`'s two
published readings, `indicator_inputLenLang` or `indicator_inputBitLang`
(`y.getD a false` on `pairEncode y (bits a)`), by unfolding the language and
`indicator_indexLang_pairEncode`. The first search matched only the `decide_eq_decide` closing;
its simp-set variants are five more members: `PathWalkMachine`'s `pathOr_len` and `pathOr_bit`,
`PathHardRegs`' `orc_bit`, and both halves of `Mult`'s private `mult_queries`. **Ruled (the
user, 2026-11-06): re-point all five in #208**, done at `0140aee2`. A grep of every code line
naming `inputBitLang` or `inputLenLang` finds no other unfolding: `TQBFARM/Machine`'s and
`Codec/Run`'s `orc_bit`/`orc_len` and `QueryReshape`'s `drop_bit`/`drop_len` already cite the
lemmas. The other readers of `indicator_indexLang_pairEncode` (`QueryReshape`'s
`drop_lang_pair`, `comp_lang_pair` and `transport`; `PathHardDecide`'s `qLang` step) read other
languages, which have no published reading; they are not members. Census after widening: one
declaration in each of the eight files, `PathWalkMachine` two. **Retired on #208's merge.**

**NZ-1, no NDTM branch halts in zero steps** (found 2026-11-06 in gate 102's round-1 search;
a promotion candidate, **awaiting the user's acknowledgment**). The deterministic fact is public
(`Turing.FinTM.not_computesInTime_zero`, `TuringMachine/Finite`) and cited where it applies. Its
nondeterministic analogue (`Cfg.init` is live, so `N.tm.HaltsWithin z 0` fails) has no public
lemma and is proved twice: `ClassNP/ExhaustiveReplay`'s private `xr_not_haltsWithin_zero` and an
inline step of `ClassNP/NDNormalForm` (`hpos`, through `runWith_nil`, `initCfg_eq` and
`Cfg.init_state`). One member in each file. **Proposed disposition:** the dedup window (12.2c):
publish `NDTM.not_haltsWithin_zero` beside the NDTM run equations and re-point both.

**TC-1, the copying transducer state** (PR #164, A1, 2026-10-25; gate 76's note 7). One fact, a
transducer started in a state that copies every bit and is kept is the identity, in three files:
- `Complexity.transduce_of_copy` (public, `ClassNP/Transducer`, line 83, new in #164), the general
  form: from `∀ b, δ q b = q` and `∀ b, o q b = some b`, `transduce δ o q l = l`;
- `Complexity.KarpLipton.transduce_drop_true` (public, `CircuitComplexity/KarpLiptonPrefix`, line
  87) and `Complexity.Meyer.transduce_fT_copy` (public, `CircuitComplexity/MeyerVerifierGlue`,
  line 145): its instances at `q = true` and `q = none`, each the general lemma with `fun _ => rfl`
  twice (the megafill D review's `probe/A1ConsumerProbe`; gate 76 checked both specializations),
  each re-proved by its own induction.

Both instance files import `ClassNP/Transducer`, so each can cite the general form.
`spaceConstructible_poly`'s landing cites it (`Savitch`'s private `scp_transduce_copy` is the
one-line application), which avoids a third copy. **The ruling (user, 2026-10-25, Q-D2): include
the general form in A1; re-point the two instances in the user's dedup window (12.2c), since that
edits `CircuitComplexity/*`.** Census (one member per file, at A1's head): `ClassNP/Transducer` 1 of
10 declarations (10.0%), `KarpLiptonPrefix` 1 of 16 (6.3%), `MeyerVerifierGlue` 1 of 42 (2.4%). The
one-fifth rule is not reached.

**RS-1, the restart identity** (PR #170, B5a's landing, 2026-10-27; disclosed in gate 81's pack,
item 4; completed by gate 81's finding 1). One fact: a machine whose initial state is a relabelled
`q` starts in the relabelled blank configuration at `q`, i.e.
`B.q₀ = f A.q₀ → B.initCfg x = (A.initCfg x).mapState f`. It is proved at five sites in four
files, each by `Cfg.ext` with the `Cfg.init_*` and `Cfg.mapState_*` field equations:
- `Turing.UniversalK`'s `uk_init_mapState` (private, line 1816), the general form, used twice
  (`uk_loop_init`, the suffix startup);
- `Turing.UniversalK`'s `exists_selfStartupTMK` (public, line 1425): its local `hinit`
  (line 1584), `R.initCfg (pairEncode α w) = d₀.mapState Sum.inl` with
  `R := { W with q₀ := Sum.inl A.q₀ }` (gate 81's finding 1);
- `CodeSimulator`'s `us_start` (private, line 8984 at #170's head), its instance at
  `{ W with q₀ := Sum.inl entry }`, after `MultiTapeTM.initCfg_with_q₀`;
- `ExhaustiveReplay`'s `xr_E_initCfg` (private, line 3133), its instance at a doubled `Sum.inl`
  with the host's blank fields;
- `NTimeHierarchy`'s `un_setup` (private, line 604): its local `hstart` (line 1410), the instance
  at a seven-fold `Sum.inl` of the embedded blank start `c0`.

Census (one member per file; each count at the tree named): `CodeSimulator` 1 of 208 declarations at
#170's head (12 public, 196 private; 0.5%), `ExhaustiveReplay` 1 of 185 (0.5%), `UniversalK` 2 of 79
(2.5%), `NTimeHierarchy` 1 of 15 at the campaign tip before #172 (6.7%), 1 of 25 after it (4.0%;
cumulative with TR-1 below). The one-fifth rule is not reached. **Disposition** (gate 81's finding
1: publication need not precede #170 under D1(A)): a public row beside `MultiTapeTM.initCfg_with_q₀`
(`TuringMachine/Finite`) in the user's dedup window (12.2c), with the five sites re-pointed.

**PL-1, the linear-to-polynomial lift, and WT-1's residue** (PR #171, the word tests, 2026-10-27;
disclosed in gate 82's pack, item 5). Two copies outside the ruling's scope (E-DUP covered the
fixed-word and all-`true` tests only):
- `Nondeterminism`'s private `a3n_poly_linear` (line 3537 at #171's head `d17f63c8`; 13 uses) and
  `a3n_poly_const` (line 3544), equal in their proofs, up to the names, to the public
  `Complexity.polyTimeComputable_of_linear` and `Complexity.polyTimeComputable_const`
  (`ClassNP/PolyTimePairing`, lines 64 and 71). `Nondeterminism` does not import `PolyTimePairing`;
  the import is acyclic (`PolyTimePairing` imports only `ClassNP/PolyTime` and `Build/Primitives`).
- `Savitch`'s inline `hD'` (`SpaceComplexity/Savitch`, line 193 in `spaceConstructible_poly`'s
  proof): the conversion of `computesFunInTime_ifEq [] [true] [false]` to `[decide (x = [])]`,
  which is `Turing.FinTM.computesFunInTime_decideEq []` (#171). An inline step, not a declaration.
  **Re-pointed by #175's round-1 fix** (gate 86's finding 2, user, 2026-10-27): the proof, now in
  `Constructible`, takes its decider from `computesFunInTime_decideEq []`; no copy is left there.
- `SAT`'s private `sat_pt_eq` (line 2886) and `CookLevin/Hardness`'s private `clA5_pt_eq` (line
  6818), twins (found by gate 82's resolution of its finding 1): each lifts
  `computesFunInTime_ifEq w [true] [false]`, converts it to `[decide (x = w)]` and composes it with
  a polynomial field map. Each is `polyTimeComputable_of_linear (computesFunInTime_decideEq w)`
  composed with that map.

Census (one member per file, at #171's head): `Nondeterminism` 2 of 199 declarations (8 public, 191
private; 1.0%), `PolyTimePairing` 2 of 26 (7.7%; the public originals), `SAT` 1 of 270 (0.4%),
`CookLevin/Hardness` 1 of 545 (0.2%). **Corrected (gate 86's finding 2, 2026-10-27):** the census
omitted the fixed-word test's public original, `Build/WordTests`'s `computesFunInTime_decideEq`,
**1 of 4 declarations (25%)**, so the source-inclusive count crosses one fifth in `WordTests`.
**Human review (user, 2026-10-27): accepted** — a four-declaration module whose member is the
public row the copies should cite; the consumers' re-points retire the family. **Disposition:** the
user's dedup window (12.2c): re-point the two privates to the public rows (one import), and the
twins to `computesFunInTime_decideEq w` (each with the import of `Build/WordTests`); `hD'` is
re-pointed already (#175).

**TR-1, the truncation of an acceptance at an all-branch budget** (PR #172, H's landing,
2026-10-27; the H brief review's F1 and gate 84's pack, item 5). One fact: if every branch of `N`
on `x` halts within `T`, an acceptance at any length is an acceptance within `T` (and conversely
by `AcceptsWithin.mono`). It is stated privately in three files:
- `Nondeterminism`'s `acceptsWithin_iff_of_halts` (line 165), through the published
  `Turing.run_take_of_halted`;
- `ExhaustiveReplay`'s `xr_accepts_iff_of_halts` (line 134);
- `NTimeHierarchy`'s `nh_accepts_of_halts` (new in #172), through `run_take_of_halted`. The
  user's D1 (A) licensed this leaf; the v3 screen pairs it with the first at 61%.

`ClassNP/NTIME`'s `NTIME.mono` does the same truncation inline. Census (one member per file, at
#172's head `33d68537`, a tree before #171): `Nondeterminism` 1 of 201 (8 public, 193 private; 0.5%;
1 of 199 after #171), `ExhaustiveReplay` 1 of 185 (0.5%), `NTimeHierarchy` 1 of 25 (4.0%).
**Cumulative across families** (gate 84's finding 1): after #172, `NTimeHierarchy` carries RS-1's
`un_setup` and TR-1's `nh_accepts_of_halts`, **2 of 25 (8.0%)**. No file reaches one fifth.
**Disposition:** the user's dedup window (12.2c): publish the truncation beside
`FinNDTM.AcceptsWithin.mono` (`ClassNP/NTIME`, which would import `ChoiceWords`; no cycle), and
re-point the three.

**LS-1, the logarithmic bound below the linear one** (PR #175, the move of
`spaceConstructible_poly` to `Constructible`, 2026-10-27, pending its merge; gate 86's pack, item 3).
One fact, `logSpace n ≤ n + 1`, in three places:
- `Machines/ARMWidth`'s public `Complexity.logSpace_le_succ` (line 51), the lemma (a colleague's
  file, outside `Constructible`'s closure);
- `Constructible`'s `spaceConstructible_poly`, the dominance step, inline through `logSpace_eq` and
  `Nat.log_le_self` (before #175 it cited `logSpace_le_succ` from `Savitch`, whose closure has
  `ARMWidth`);
- `Constructible`'s `spaceConstructible_linear`, its dominance conjunct, inline as
  `Nat.succ_le_succ (Nat.log_le_self 2 n)` by reduction of `logSpace` (another file's definition;
  the proof predates rule 10).

Two inline steps and one declaration; the one-fifth rule is not in question. **Accepted (user,
2026-10-27; gate 86's finding 1)** as debt, the new inline step included. **Disposition:** the
user's dedup window (12.2c): move `logSpace_le_succ` into `SpaceComplexity/Basic` beside
`logSpace_eq` (a mechanical edit in `ARMWidth`, FYI to its author), and re-point the two inline
steps to it. **Brought forward (user, 2026-11-04): PR #181** (gate 89) does exactly that, and also
moves `logSpace_le_of_le_mul_two_pow` to `Basic` and `LOGSPACE_subset_PSPACE` and
`SPACE_succ_pow_subset_PSPACE` to `SpaceClasses`. **LS-1 is retired when #181 merges.**
**Scope corrected (gate 89, round 1, major 1).** Two further inline copies predated #181:
- `narm_decides` (`Machines/NARMProof`);
- `narm_logspace_ptm` (`Machines/NARMLogspace`).

Both are `have hLn : logSpace n ≤ n + 1` by `Nat.log_le_self` and `simp only [logSpace]`, in
Hydroxyi's files, and neither was in this entry. Round 2 of #181 (`1d1247a3`) re-points both to
`logSpace_le_succ`, a mechanical ARM dedup edit (FYI). A search of the round-2 head
(`campaign/gates/89-space-facts-api/evidence/round2/ls1-search/`) finds the fact stated only in
`Basic` and cited everywhere else.
**Scope corrected again (gate 89, round 2, major 1).** Two more inner steps derived the logarithm's
form of the fact, `Nat.log 2 m + 1 ≤ m + 1`:
- `ImplicitlyLogspaceComputable.computesInSpace` (`ImplicitPoly`, Hydroxyi's ARM-program file):
  `W ≤ F + 2` with `W = Nat.log 2 (F + 1) + 1`;
- `mem_LOGSPACE_preimage` (`Logspace/PreimageHost`, the campaign's).

Round 2's search had classed both as "polylogarithmic bounds": true of the enclosing bounds, not of
these steps. Round 3 of #181 (`8d41671c`) re-points both to `logSpace_le_succ` through
`logSpace_eq`. Its exhaustive classification of every `Nat.log_le_self` use and every
`logSpace`-by-successor statement
(`campaign/gates/89-space-facts-api/evidence/round3/ls1-search/classification.md`) finds the fact
proved once, in `Basic`, and cited at eight sites.
**Scope corrected a third time (gate 89, round 3, major 1).** Round 3's search had looked for
`Nat.log_le_self` only, so it missed one more inline copy: `arm_decides` (`Machines/ARMProof`,
Hydroxyi's) proved `hLn : Ls ≤ n + 1`, with `Ls := logSpace n`, by unfolding `logSpace` and citing
`Nat.log_lt_self`. Round 4 of #181 (`a7c2a655`) re-points it to `logSpace_le_succ` (a mechanical ARM
dedup edit, FYI). Round 4's search covers every line that touches `logSpace`'s definition and every
Mathlib upper bound of `Nat.log`
(`campaign/gates/89-space-facts-api/evidence/round4/ls1-search/classification.md`). It finds the
fact proved once, in `Basic`, and cited at nine sites.

**LS-2, the logarithmic bound by the binary length** (gate 89, round 4's search; ruled with it, user,
2026-11-04: "Fix in #181 now"). The fact is `logSpace n ≤ Nat.size n + 1`, equivalently
`≤ |bits n| + 1`; its converse is `|bits n| ≤ Nat.log 2 n + 1`. Before round 4:
- the public `Complexity.LogProg.ISCount.logSpace_le_size_succ` (`Logspace/ISCountMath`);
- inline re-derivations in `Randomized/BPLInP`, twice (`two_pow_codes_le`, `BPL_subset_P`);
- the public `Randomized.PolyAmp.logSpace_le_ell` (`Randomized/SpaceAmplifyPoly`, its `ell n` is
  `|bits n| + 1`), re-proved through `Nat.log_lt_of_lt_pow`;
- the converse, published as `LogProg.length_bits_le_log` (`Machines/Bin`) and re-derived by the
  private `size_le_logSpace` (`Logspace/ISCountGenCorrect`).

All in Hydroxyi's files. `BPLInP` did not import `ISCountMath`. **Retired by #181, round 4**
(`fe4bdb67`, `227d92ee`): `logSpace_le_size_succ` moves verbatim to `SpaceComplexity/Basic` as
`Complexity.logSpace_le_size_succ`, and the four re-derivations cite it or `length_bits_le_log`
(copy deletions and re-points, FYI). Same round, same ruling: `ExpBFS/Run`'s `setup_run` cites its
own file's `lgv_le_succ` for `hv |x| ≤ |x|` instead of re-deriving it (`252bbcb8`).

**LS-3, the binary length as the logarithm** (gate 89, round 4's search). The fact is
`|bits n| = Nat.log 2 n + 1` for `n ≠ 0`. No public lemma states it. Private copies:
- `Constructible`'s `b3a_bits_length` (the campaign's);
- `Randomized/QuasiPolyHierarchy`'s `length_bits_eq` (Hydroxyi's);
- `Diagonalization/NTimeDiagonalizer`'s `qy_log_bits`, with `Nat.size n = Nat.log 2 n + 1` also
  inline in its `qy_two_pow_bits_le` (E-D's file, in flight).

**Census** (gate 89, round 4's minor 2; members over all declarations, private included):
- `Constructible` 1/28;
- `QuasiPolyHierarchy` 1/25;
- `NTimeDiagonalizer` 2/236 (`qy_log_bits` and `qy_two_pow_bits_le`'s inline equality).

None reaches one fifth. The halves of these equalities also prove LS-2's converse
(`QuasiPolyHierarchy:63`, `NTimeDiagonalizer:430`, `:446`); they stay within LS-3, and the one
public converse lemma is `LogProg.length_bits_le_log`. **Accepted (user, 2026-11-04)** as debt.
**Disposition:** the dedup window (12.2c): publish the equality beside `LogProg.length_bits_le_log`
and re-point all four occurrences (the three privates and the inline step) after E-D lands.

**BL-1, elementary bounds on the binary length** (gate 89, round 4's binary-length sweep,
`campaign/gates/89-space-facts-api/evidence/round4/ls1-search/bitsweep.tsv`). One- and two-line
steps that carry a Mathlib `Nat.size` fact over to `|Nat.bits n|` through `Nat.size_eq_bits_len`,
where a lemma already states the bound:
- (i) `|bits n| ≤ m` from `n < 2 ^ m` (`LogProg.length_bits_le`, `Machines/Bin`): `Meyer:189`,
  `MeyerTableau:437`, `ISCountGenCorrect`'s private `bits_succ_le` (`:210`);
- (ii) monotonicity (`LogProg.length_bits_mono`): `NTimeDiagonalizer`'s private `qy_bits_len_mono`,
  `RecordTable:2762`, `InputLength:418`, `:420`, `Catalog:4125`;
- (iii) `|bits n| ≤ n` (`Turing.length_bits_le_self`, `TuringMachine/Encoding`):
  `CodeSimulator:1448`, `NTimeDiagonalizer:455`, `SpaceAmplifyPoly:287` (`ell_le`),
  `RecordTable:2764`, `:4256`;
- (iv) `n < 2 ^ |bits n|`: public as `Randomized.PolyAmp.lt_two_pow_bits` and, for `posWidth`,
  `Turing.record_pos_lt`; inline or private in `NTimeDiagonalizer`'s `qy_lt_two_pow_bits`,
  `Logspace/Mult:254`, `:255`, `WindowClock:119`;
- (v) `2 ^ |bits n| ≤ 2n` or `2n + 1`: public as `Complexity.Codec.two_pow_bits_le` (`Codec/Layout`)
  and `Randomized.PolyAmp.two_pow_bits_le`; inline or private in `Codec/Parse:90`,
  `NTimeDiagonalizer`'s `qy_two_pow_bits_le`, `BPLInP:399`.

The files are the campaign's, Hydroxyi's, E-D's in-flight `NTimeDiagonalizer` and the
colleague-owned `CircuitComplexity/Meyer*`. `Machines/Bin` sits above the `CircuitComplexity` and
`TuringMachine` layers, so several sites cannot import it. Each site is one step, so the one-fifth
rule is not in question. **Accepted (user, 2026-11-04)** as debt. **Disposition:** the dedup window
(12.2c): one home for the five bounds below both layers (beside `Turing.length_bits_le_self`), then
re-points where the imports allow. `CircuitComplexity` needs its own authorization.
**Scope corrected (gate 89, round 4, major 1).** The list above missed:
- `Codec/Layout`'s `wP_le` (iii, through logarithms);
- `PathHard`'s `two_pow_ell_le` (v) and `ell_mono` (ii);
- `RandomWalkPad`'s `padDegree_le` (v);
- `PrimeFind:204`, `:318` and `TQBFHardParams`' `wP_le` (iii).

With `Layout`'s `wP_le`, `Layout` stood at 2 of 9 declarations. **Ruled (user, 2026-11-04): "Re-point
now in #181."** Round 5 of #181 (`d789d6db`, `98912ab2`) re-points every site whose file can reach
a canonical lemma:
- (v) `two_pow_bits_le` moves from `Codec/Layout` to `Machines/Bin`. `Parse:90`, `PathHard`'s
  `two_pow_ell_le`, `RandomWalkPad`'s `padDegree_le`, `BPLInP:399` and `PolyAmp.two_pow_bits_le`
  cite it;
- (iii) `Layout`'s `wP_le` cites `Turing.length_bits_le_self` through the new `Codec.wP_eq`, and
  `TQBFHardParams`' `wP_le`, a restatement of `Codec.wP_le`, is removed. `PrimeFind:204`, `:318`,
  `CodeSimulator:1448`, `RecordTable:2764`, `:4256` and `SpaceAmplifyPoly`'s `ell_le` cite
  `length_bits_le_self`;
- (i) `ISCountGenCorrect`'s `bits_succ_le` cites `length_bits_le`;
- (ii) `PathHard`'s `ell_mono` cites `length_bits_mono`;
- (iv) `WindowClock:119` cites `record_pos_lt`.

`Layout` now has no member. **The residual**, every member of the sweep's classification at
#181's round-5 head (`campaign/gates/89-space-facts-api/evidence/round5/ls1-search/bitsweep-classes.md`):
- (i) `Meyer:189` and `MeyerTableau:437`: colleague-owned `CircuitComplexity`;
- (ii) `RecordTable:2762`, `InputLength:418`, `:420` and `Catalog:4125`: `Machines/Bin` is above
  these files;
- (iv) `Mult:254`, `:255`: no (iv) lemma that this file can reach. `PolyAmp.lt_two_pow_bits` and
  `Turing.record_pos_lt` are two public statements of (iv) in different layers and forms;
- `NTimeDiagonalizer`, E-D's file in flight:
  - (ii) `qy_bits_len_mono`;
  - (iii) `qy_call_bound:455`, which E-D's landing already re-points;
  - (iv) `qy_lt_two_pow_bits`;
  - (v) `qy_two_pow_bits_le`;
  - (iv) **`qy_ones_ge:415–417`, new in round 5's sweep** (two inline `Nat.lt_size_self` steps); **acknowledged (user, 2026-11-04)**. The acknowledgment was asked on the
    premise that E-D's landing re-points it. That premise was wrong: the file does not reach `Machines/Bin`,
    so its disposition is the dedup window.

**Disposition of the residual:**
- E-D's landing PR re-points `qy_call_bound:455` (iii), since the file reaches `Encoding`;
- `NTimeDiagonalizer`'s other four members cannot reach `Machines/Bin`, like `RecordTable`'s, and go
  to the dedup window with the rest;
- `CircuitComplexity` comes under its own authorization.

**Scope by kind (gate 89, round 5, majors 1 and 2; ruled by the user, 2026-11-04: "Acknowledge,
scope by kind").** BL-1's acknowledged scope is every re-derivation of kinds (i)–(vi) anywhere in
TCSlib, whether or not a sweep lists it. A member found later is an accounting correction (a minor,
TEMPLATE failure mode 5), unless it pushes a file past one fifth. The kinds are:
- (i)–(v), above;
- **(vi)**, new: the word-value bound `bitsVal w < 2 ^ |w|` (`LogProg.bitsVal_lt_two_pow`,
  `Machines/Bin`).

Round 5's audit found five members outside the site lists, all predating #181 and all acknowledged:
- (v) `Logspace/QueryReshape`'s private `query_index_bound` (sweep group 90) and
  `Randomized/UniformSample`'s `le_two_pow_size_pred` (group 62), whose positive branches derive
  `2 ^ size n ≤ 2n` natively. Both files reach `Machines/Bin`. `UniformSample` is Hydroxyi's;
- (i) `CookLevin/Hardness`'s private `clCount_width`, by binary induction, and (iii) its
  `clElapsed_width`, through `clCount_width`. `Hardness` reaches `Encoding` but not `Bin`;
- (vi) `Codec/Word`'s `Complexity.Codec.bitsVal_lt_two_pow`, an exact copy of `Bin`'s, which
  `Word` imports. `Word` is Hydroxyi's. Its users would resolve to `Bin`'s through `open LogProg`.

**Census:**
- `QueryReshape` 1/120, `UniformSample` 1/19, `Hardness` 2/545, `Word` 1/47;
- `Bin`'s five members (`length_bits_le`, `length_bits_mono`, `two_pow_bits_le`,
  `length_bits_le_log`, `bitsVal_lt_two_pow`) are the canonical statements the copies re-point to,
  not copies. That makes 5/15, recorded as the one-fifth review item.

**Disposition:** the dedup window, with the rest. The one home below both layers re-points them
once.

**CL-1, the codec languages' sibling idiom** (gate 91, the edge-mode PR's screen; ruled with it,
user, 2026-11-04). Each code language of `SpaceComplexity/Codec` has its own definition, its own
membership lemma at an encoded input (`mem_validLang`, …), its own characterization through the
word-level check (`validLang_iff`, …) and its own decider proof (`validLang_mem`, …). The proofs
repeat two pieces: the decoding of `⟨x, ⟨bits c, bits s⟩⟩` (`pairEncode_inj` twice, then
`bits_injective`) and the decider wrapper (`arm_decides_poly` on `CA`, the `one_run` case split and
the reject branch). The four languages `validLang`, `initLang`, `acceptLang` and `stepLang`
(Hydroxyi's) already formed 31 copy pairs at the base. The edge-mode PR adds `edgeLang`,
`mem_edgeLang`, `edgeLang_iff` and `edgeLang_mem`, 25 more pairs. About 25 lines of shared text
are the decoding proofs and the wrapper's skeleton. The edge mode's own correctness proof
(`edge_round`, `edge_loop`, `edge_tail`) is in no pair. **Census** (gate 91, minor 3; members of the
family over all declarations, private included): `Langs` 8/9 → 10/12, `Checks` 4/26 → 5/31,
`Deciders` 3/16 → 4/22. `Langs` was already above one fifth at the base, from the four existing
languages; the acceptance above covers it. The edge member crosses no new file's threshold.
**Accepted (user, 2026-11-04)** as debt. **Disposition:** the dedup window (12.2c): one membership
lemma for languages of encoded triples, and one decider wrapper parameterized by the mode's tail,
with the five languages re-proved through them. This reworks Hydroxyi's proved deciders, interface
design that waits for him.

**RO-1, the one-step identity `M.runFrom c 1 = M.step c`** (PR #176, E-Q cont1's landing,
2026-10-27; its review's F5; ruled with the landing, user, 2026-10-27). No public lemma states it
(`MultiTapeTM.runFrom` is in the vendored `Deterministic`). Private copies: `NTimeDiagonalizer`'s
`qy_run_one` (new), `ExhaustiveReplay`'s `xr_runFrom_one`, `SAT`'s `satRed_one`, `CfgRecord`'s
`recordStep_runFrom_one`; inline in 13 declarations (`SeamLayout` 3, `Catalog` 4, `Primitives` 4,
`Loop` 1, `Encoding` 1). Census (declaration members, at #176's head): `NTimeDiagonalizer` 1 of 236
(0.4%), `ExhaustiveReplay` 1 of 185 (0.5%), `SAT` 1 of 270 (0.4%), `CfgRecord` 1 of 138 (0.7%),
`SeamLayout` 3 of 36 (8.3%), `Catalog` 4 of 505, `Primitives` 4 of 285, `Loop` 1 of 205, `Encoding`
1 of 61. The one-fifth rule is not reached. **Disposition:** the dedup window (12.2c): a public
`MultiTapeTM.runFrom_one` in a non-vendored module, and the 17 sites re-pointed.
**+1 (G5's landing, #211; gate 102):** `Robustness/TwoTapes`' `tt_round` closes the one-step
identity inline (`runFrom_succ_eq_step.trans runFrom_zero`), 1 of 104 declarations; 18 sites for
the window.

**NB-1, the `Nat.bits` arithmetic family** (PR #176; the review's F2). `NTimeDiagonalizer`'s
`qy_two_pow_bits_le` (the statement of `SpaceAmplifyPoly`'s `two_pow_bits_le`, on `main`) and
`qy_log_bits` (whose `≤` half is `Machines/Bin`'s `length_bits_le_log`); before E3 also
`qy_bits_len_mono` (`Bin`'s `length_bits_mono`) and `qy_lt_two_pow_bits`, now through Mathlib's
`Nat.size` facts; and, inline, `qy_call_bound`'s `(Nat.bits (f a)).length ≤ f a`, the statement of
`Encoding`'s `Turing.length_bits_le_self` (gate 87's finding 2). Census, source-inclusive (gate 87's
finding 3; declaration members, inline steps counted as in RO-1): `NTimeDiagonalizer` 3 of 236
(1.3%), `Machines/Bin` 2 of 12 (16.7%), `SpaceAmplifyPoly` 1 of 20 (5%; `two_pow_bits_le`, on `main`
and on the campaign since its merge of `main`), `Encoding` 1 of 61 (1.6%; `length_bits_le_self`);
the last three are the public originals. Below one fifth. **Disposition:** `qy_call_bound`'s step
re-points to `length_bits_le_self` in E-D's landing (ruled, user, 2026-11-04); the rest in the dedup
window: a shared `Nat.bits` module.

**Cumulative per-file accounting for RO-1 and NB-1** (source-inclusive; gate 87's finding 3).
`NTimeDiagonalizer` 4 of 236 (1.7%: RO-1 1, NB-1 3; 3 after E-D's landing re-points
`qy_call_bound`); `Encoding` 2 of 61 (3.3%: RO-1 1, NB-1 1). Every other file is in one of the two
families only, its census above. No file approaches one fifth.

**RC-1, row candidates from E-Q cont1** (PR #176; the brief's and the report's, the review's F9).
Private leaves and lemmas with no published counterpart, each a candidate public row: the clocked
install call (`QyClockSpec`, `qy_clocked_call`, `qy_clockHost_*`); the framed length comparison
with verdict (`qyCmpTM`, `qy_cmp_run`); the repeating emitter (`qyEmitTM`, `qy_emit_run`,
`qy_emit_stop`); the phase host's segment forms (`qy_hosted*`, `qy_round_of_seg`); the
`Nat.unpair` successor rule (`qy_unpair_succ_*`). Not copies. **Disposition:** promotion when a
second consumer appears, or in the dedup window.

**QF-1, two in-file factorings** (PR #176; the review's F6). The `copyMapTM`/`transferMapTM`
endpoint conversion and the `clockCfg` field conversion recur in `NTimeDiagonalizer` (pairs at
90–94%, justified as readings of different rows). Optional. **Disposition:** the dedup window.

**RC-2, a framed take-one-cell row** (E-D's brief, 2026-11-04; its review's F1, ruled by the user).
No published row writes a blank at one cell, and every framed row needs blanks at its word's
relative positions `-1` and `|w|`, so a word inside a nonblank block cannot be split off by
published rows. E-D's own leaf `dzTakeTM` (read the cell, blank it, step right) fills the gap,
privately. Not a copy. **Disposition:** promotion to a public framed row when a second consumer
appears, or in the dedup window.

**AS-1, machine-specific step lemmas beside the general ones** (#182, gate 90, 2026-11-04). #182
publishes one step equation per instruction (`Complexity.LogProg.astep_inc` … `astep_jeqSnd`,
`Machines/ARM`). Three older lemmas state a step of one particular machine at one label:
`LogProg.astep_call₁` (`UnaryLogspace`: `astep_call` with `vword_unary₁`), and
`BoolCircuit.AdjScan.astep_hit` and `astep_jeqFst` (`CircuitComplexity/LogspaceUniformScan`). They
are specializations, not copies; the copy-text screen pairs none of them. The last shares its short
name with the general `astep_jeqFst`, and resolves by argument type in its own file, which opens
`Complexity.LogProg`. **Disposition:** in the dedup window (mechanical ARM edits, FYI), re-prove the
three through the general equations, and rename the circuit one if the shared name is unwanted.
**Extended (gate 90, minor 3):** three more specializations of `astep_call`:
- `BoolCircuit.AdjScan.astep_rd` (`LogspaceUniformScan:196`, with `vword_unary₁`);
- `BoolCircuit.AdjWalk.astep_call₁` and `astep_call₂` (`LogspaceUniformWalk:288, 298`, with
  `vword_unary₁` and `vword_unary₂`).

That makes six members. None is a copy: the screen with `LogspaceUniformWalk` added gives
170 → 179 declarations and 46 → 46 pairs, identical
(`campaign/gates/90-arm-embed-api/evidence/round1-fix/`). Same disposition, same window.

**NF-X1, an idiom exclusion** (NF's partial delivery, review F6; ruled by the user, 2026-11-04).
`NTimeHierarchy.lean::un_setup` reproduces 57% of `NDNormalForm.lean::nf_setup`. The shared text
is three invocations of the published initial-configuration field equations
(`MultiTapeTM.initCfg_eq`, `Cfg.init_state`, `Cfg.init_workTapes`): the idiom of reading the
initial configuration, not a re-derived composite. **Disposition:** excluded; not counted.

**E-D's delivery** (`exists_diagonalizer`, #188; review `campaign/fills/eq/reviews/ed-fill/`;
ruled by the user, 2026-11-04):
- **BL-1 (vi):** `dz_word_lt` (`Nat.ofDigits 2 (w.map Bool.toNat) < 2 ^ |w|`) is a new member,
  **acknowledged** for the dedup window's single home below both layers; `NTimeDiagonalizer`
  cannot reach `Machines/Bin`. Census `NTimeDiagonalizer` (vi) 1.
- **Removed at landing:** `dz_padded_value`'s inline re-derivation of Mathlib's
  `Nat.ofDigits_append_replicate_zero` (E3), and `dz_top_run`'s inline first halt, FH-1's
  `MultiTapeTM.exists_first_halt` (E4). Recorded so that the ledger shows them caught.
- **Promotion requests:** `dz_split_stream` restates `Build/NDHost`'s private `guessRun_split`
  (98%), to be promoted or given a public `List` form; `dz_word_lt` restates `ExhaustiveReplay`'s
  private `xr_val_lt` (65%), with BL-1 (vi)'s home.
- **QF-1, extended:** `dz_initCfg` and `qy_initCfg` state one fact for different machines ("a
  phase host's initial configuration is the blank seam in normal form"); one generic lemma over
  `phaseHostTM_q₀` and `initCfg_ofWords`.
- **RC-3, row candidates:** the clocked hosted run (`DzClockSpec`, `dz_clock_exists`); the
  silent-transport reconstruction (`dz_silentCfg_eq`), beside `embedEmitCfg_eq`; and the output
  length of a computed function (`dz_out_le`, `|F y| ≤ T |y|`), also inline in `SAT`,
  `Nondeterminism`, `TMSAT` and `Build/Loop`'s private `loop_fuel_width`. **Disposition:** the
  dedup window.
- **Census, landed (gate 93, finding 4):** 8 of `NTimeDiagonalizer`'s 342 declarations (2.3%),
  deduplicated: RO-1's one, the five distinct NB-1/BL-1/LS-3 members, `dz_word_lt` and
  `dz_split_stream`. E1 retires `qy_call_bound`'s BL-1 (iii) step. Row candidates (RC-3) and
  in-file factorings (QF-1) are not counted as debt.
- **ED-IN, inline re-derivations, scoped by kind (ruled by the user, 2026-11-04, gate 93 round
  2):** any inline step in `NTimeDiagonalizer` that re-derives a published run, buffer or segment
  lemma belongs to this family, for the dedup window; a later find is an accounting minor. The
  members found so far are all removed: `dz_first` (`Segment.time_eq`), `dz_split`'s separator
  (`bufferTape_append_mid`), `dz_split_tape`'s prefix (`bufferTape_take`), `dz_top_run`'s output
  (`runFrom_output_eq_of_halt`), and three natural cells (`bufferTape_nat`).
  **Further member (gate 93 round 3, finding 1):** `qy_patch_end`'s prefix branch re-derives
  `FinTM.bufferTape_take` (and so `_take` has a counterpart, against BW-1's note); re-pointed in the
  dedup window. Census 9 of 342.
- **Removed in round 2 (gate 93, findings 1–2):** `dz_first` re-proved `Segment.time_eq`, and
  `dz_split`'s separator cell re-proved `FinTM.bufferTape_append_mid`. Both now cite them (#188
  `a64f513d`).

**NF cont1's delivery, F2: four kinds re-stated** (review
`campaign/fills/c1/reviews/nf-cont1-fill/`; ruled by the user, 2026-11-04: **publish homes
first**). An API PR publishes each fact beside its definitions before NF lands, and NF's landing
cites them:
- (i) the input read depends on the input head only (`nf_inputSymbol_congr`; privates
  `ExhaustiveReplay.xr_inputSymbol_congr`, `ZoneRebalance.zr_inputSymbol_congr`);
- (ii) a live configuration redirected to `⟨i, q⟩` is phase `i`'s tagged configuration at `q`
  (`nf_retag`; `SeamLayout`'s private `sl_rewrap`, and inline in 15 declarations);
- (iii) a configuration tagged by phase `i` is at no state of another phase (`nf_tagged_ne_park`;
  privates `CfgRecord.record_tag_ne`, `SeamLayout.sl_tagged_ne_done`);
- (vi) the length of a list of equal-length chunks (`nf_stream_length`; public as
  `Complexity.CfgTableau.length_flatMap_const` in colleague-owned `CircuitComplexity`, which
  NF cannot import).

The existing private copies are re-pointed in the API PR where the files are the campaign's.
*Numbering (gate 95, note 9):* the kinds carry the review's labels, (i)–(iii) and (vi), as in the
decision put to the user. This entry first numbered the chunk length (iv), which collided with the
review's F8 (iv), the buffer end (RC-4 below). The review uses no (v).

**RN-1, renamed configurations converted field by field, scoped by kind** (ruled by the user,
2026-11-04, with gate 94). #190 publishes the general fact, `Turing.Cfg.mapState_eq_of_fields`: a
renamed configuration equals any configuration with its data fields and the renamed state.
- **The family:** every inline proof of that fact anywhere in TCSlib (the five-line
  `Cfg.ext`/`Cfg.mapState_*` block), with the retag (ii) as an instance. A later find is an
  accounting minor.
- **Re-pointed in #190:** `CfgRecord`'s `recordStep_mapState_eq` (removed), `SeamLayout`'s
  `sl_rewrap`, and `ExhaustiveReplay`'s `xr_phase_step` (two blocks) and `xr_halt_fixed` (two
  blocks).
- **Remaining, for the dedup window** (gate 94's minors 1–2, 2026-11-05; counted as conversions
  inside declarations, not copies of their statements). By file:
  - `CodeSimulator`: `canonStageLeg0`–`6`, `canonStageOuterSpec`, `canonStageInnerSpec`,
    `us_start` (10);
  - `ZoneRebalance`: 21 of about 870 (2.4%). These are `zr_short_fields`,
    `zr_rightSeekBack_post`, `zr_rightRuler_post`, `zr_adjustedWalk_post`,
    `zr_adjustedBack_post`, `zr_writeHalves_post`, `zr_rightPass_post`, `zr_test_post`,
    `zr_body_post`, `zr_return_post`, `zr_rightReturn_post`, `zr_rightLeft_post`,
    `zr_twoSteps_fields`, `zr_leftMove_fields`, `zr_leftWrite_fields`, `zr_leftPass_fields`,
    `zr_final_fields`, `zr_extend_fields`, `zr_scanBody_fields`, `zr_scan_fields` and
    `zr_countClear_fields`. RI-1's `zr_pinLoop` is retired and not counted;
  - `NDHost`: `gr_handoff`, `guessCtlRunTM_stop_of_halted`;
  - one each in `ExhaustiveReplay` (`xr_E_initCfg`), `NDCodeSimulator`
    (`exists_ndInterpreterCore`), `Seam` (`phaseHostTM_run`), `InputRewind`
    (`Cfg.mapState_mapState`), `NTimeHierarchy` (`un_setup`; NF-X1's pair too) and `SeamLayout`
    (`exists_seamLayoutTM`).

  The NF review's F2 list has 19 names, not 15; its `xr_phase_step` and `xr_halt_fixed` are
  re-pointed. No file crosses one fifth. NF's own copies (`nf_retag`, `nf_tag`, …) are checked at
  NF's landing (#191), where they cite `CfgFacts`.
The 15 inline (ii) steps and `CircuitComplexity`'s lemma go to the dedup window (the latter under
its own authorization). Also removed at NF's landing: `nf_all_cons`'s re-derivation of Mathlib's
`Nat.forall_lt_succ_left'` (E1).

**RN-1, an accounting minor at NF's landing** (gate 95, minor 3; 2026-11-05). `NDNormalForm`'s
`nf_pack` proved its local `hinit`, `(H.relabelState e).initCfg x = (H.initCfg x).mapState e`
(lines 62–69 at #191's head `e8994dc1`), by the five-line block: an RN-1 member that the list
above did not name. It is inside the family, so a minor. #191's repair commit `10c01517` cites
`(Cfg.mapState_eq_of_fields …).symm` there, as `nf_tag` does since `5732d5bd`. The file's other
eleven `Cfg.ext` blocks (`nf_sweep_run`, `nf_entry` and nine leaf-run endpoints) are
configuration-record equations, not renamings, so they are not members. Census: `NDNormalForm`
1 of 104 declarations at `e8994dc1`, none at `10c01517`.

**NF's landing, gate 95's major 1: repaired, no new family** (#191; ruled by the user,
2026-11-05: **repair**). At the landed head `NDNormalForm` imports `TuringMachine/BufferWords`,
but three inline steps still re-proved its identities, outside every acknowledged family (ED-IN
is scoped to `NTimeDiagonalizer`, BW-1 to `StepBlock`'s privates, RN-1 to renamings):
- `nf_bClear`'s `hw`, `bufferTape R (p + i) = bufferTape (R.drop i) p` for `0 ≤ p`, by
  `bufferTape_nat` twice and `List.getElem?_drop`: that is `FinTM.bufferTape_drop`;
- `nf_aReturn`'s `hw` (cell `|s|`) and `nf_region`'s cell `|R|`, blank at the buffer's end by
  `bufferTape_nat` and `List.getElem?_eq_none`: that is `FinTM.bufferTape_eq_none_of_not_mem`.

The steps came from the brief's own route probes, written when the fill could not import
`BufferWords`. #191's repair commit `10c01517` cites the two lemmas at the three sites, and no
member remains. Recorded so that the ledger shows them caught.

**Gate 95's round-2 major 1** (#191; repaired, the round-1 ruling's kind): `nf_split`'s local `h0`
rebuilt a list from its indexed entries by `List.ext_getElem`, re-proving Mathlib's
`List.ofFn_getElem` (with the index length moved by `List.ofFn_congr`). #191's commit `dfc3e990`
cites the two lemmas. No family; recorded so that the ledger shows it caught.

**The library sweep that followed** (gate 95, round 3; `evidence/round3/sweep/`). Every `have`,
`obtain` and private theorem of the file about core or Mathlib objects only, probed by `exact?`
in place, as a generalised `example` and as its normalised core with `apply?`. It found eight
further inline re-proofs, all of one published lemma each:
- `Nat.succ_mod_succ_eq_zero_iff` (`nf_ctl_position`), `Nat.pos_of_mul_pos_left`
  (`nf_display_firstStop`, `nf_firstStop_records`), `Nat.div_lt_of_lt_mul`
  (`nf_display_firstStop`), `Nat.mul_div_cancel'` (`nf_firstStop_records`);
- `List.ofFn_eq_nil_iff` (`nf_split`), `List.ne_nil_of_length_pos` (`nf_V_display`,
  `nf_forward`; the file already cited it twice).

It also found two rewrite chains that are each one lemma: `List.length_take` with
`Nat.min_eq_left` is `List.length_take_of_le` (eight sites), and `List.foldl_append`,
`foldl_cons`, `foldl_nil` on `l ++ [x]` is `List.foldl_concat` (seven sites). Separately,
`nf_prefix_last` and `nf_sweep_record` proved the same completion of the parser's prefix array;
it is now one private, `nf_update_last`. #191's commit `49c4d0f7` repairs all of them, with no
statement change. No family; no member remains.

**Gate 95's round-3 major 1**: one more member, which the sweep's candidate list missed because it
is an untyped `have`. `nf_display_firstStop`'s `he` (`Nat.mod_add_div`, then the zero remainder)
re-proved `Nat.mul_div_cancel'`; #191's commit `698dcdf5` cites it. The sweep now also takes every
untyped `have`/`obtain` on a core or Mathlib term with a later rewrite `at` it (gate 95,
`evidence/round4/sweep/`); the one other such site, `nf_display_flag`'s `hm`, has no library
statement. No family; no member remains.

**Gate 95's round-4 major 1**: one more fold-concatenation member, in `nf_ctl_position`'s
`simp only` set, which the round-3 sweep had wrongly exempted as a simp set. #191's commit
`b4af93b7` cites `List.foldl_concat`. The sweep now checks every member of both chain classes
anywhere in the file (gate 95, `evidence/round5/sweep/`). No family; no member found by that
check.

**RC-4, row candidates from NF cont1** (the cont1 review's F8, 2026-11-04; completed by gate 95's
note 9, 2026-11-05). The review's list "for the ledger" named F8's row candidates; they were not
carried here until now.
- **The first halting time of a choice word**, FH-1's kind for `NDTM.runWith`: `Nat.find` over
  the run's prefixes (`find_spec`, `find_min`, `find_min'`), then the output after the halt by
  `NDTM.runWith_append` and `NDTM.runWith_of_halt`. FH-1's public form,
  `MultiTapeTM.exists_first_halt`, is deterministic, and no `NDTM` form exists. It runs inline at
  two sites: `NDNormalForm`'s `nf_forward` (lines 3097–3127 at #191's head `e8994dc1`) and
  `ExhaustiveReplay`'s `xr_replay_host` (lines 2179–2189 at the campaign tip). Neither
  re-derives a lemma. **Disposition:** a public `NDTM` first-halt row in the dedup window
  (12.2c), cited at both sites.
- **(iv) a buffer is blank at and past its end** is not a row candidate after all: the review's
  "no public form" held only at the fill's frozen imports. `FinTM.bufferTape_eq_none_of_not_mem`
  (`TuringMachine/BufferWords`, public since PR #140; BW-1) states it. NF's three inline sites
  cite it: `nf_entry` since `4354cbeb`, `nf_aReturn` and `nf_region` since `10c01517` (major 1
  above). `CodeSimulator`'s private `canonStageBuffer_none` (lines 5040–5043 at the campaign
  tip; six invocations at five locations: lines 5203, 6422, 6566, 6778 and twice at 7022, corrected
  by gate 95's round-2 minor 3) restates it for cells at or past the end. **Disposition:** the dedup
  window (12.2c): re-point all six invocations to `FinTM.bufferTape_eq_none_of_not_mem` and delete
  it.
  `CodeSimulator` does not import `BufferWords` yet; the import is acyclic (`BufferWords`
  imports only `Simulation`).

Census (members over all declarations, as the style lint counts them, at the campaign tip):
`CodeSimulator` 1 of 208 (`canonStageBuffer_none`). With CC7-1's eleven and RN-1's three others
(`canonStageOuterSpec`, `canonStageInnerSpec`, `us_start`, the last also RS-1's), the file holds
15 of 208 (7.2%). The first-halt sites are row candidates and are not counted, as in RC-1–RC-3.
The one-fifth rule is not reached.

**WS-1, one step keeps a configuration in a window, and window monotonicity, scoped by kind**
(#196, the deepening's API; gate 96, major 2; acknowledged by the user, 2026-11-05, and widened by
kind the same day). #196's public `Turing.Cfg.InWindow.apply_of_lt` (`Build/CfgRecord`)
re-derived its own file's private `recordStep_window` (line 679 at #196's head `89f4ebbc`), and
one of its steps repeated `ExpBFS.inWin_mono`'s second component verbatim. The v3 screen paired
none of them (the proofs are restructured), and no family covered the kind, so it was a debt
major.
- **Ruled (user, 2026-11-05): harvest.** On #196's repaired head `b1b5199b`, `recordStep_window` is
  public as `Turing.Cfg.InWindow.apply_iff`, over any alphabet, beside the new
  `Turing.Cfg.InWindow.mono`; `apply_of_lt` is proved from the two; and the record step
  (`recordStep_observed_action`), the private lemma's one use, cites `apply_iff`.
- **The family, acknowledged by kind for 12.2c (user, 2026-11-05), widened by kind (user,
  2026-11-05):** every proof, anywhere in TCSlib, that one step keeps a configuration within a
  window of any shape (the radius window `Cfg.InWindow`, a per-tape radius, an interval, a
  visited interval), and every proof of window monotonicity. A later find is an accounting minor.
  The canonical statements:
  - `Turing.Cfg.InWindow.apply_iff`: for `c` in the radius-`s` window, `(a.apply c).InWindow s`
    holds iff no work head is at `-s` moving left or at `s` moving right;
  - `Turing.Cfg.InWindow.mono`: `c.InWindow s → s ≤ s' → c.InWindow s'`;
  - **the tape half**, to be published in the 12.2c window: an action changes a work cell only
    under that tape's old head (`z ≠ c.workTapePos i → (a.apply c).workTapes i z =
    c.workTapes i z`). It exists today as `TuringMachine/Oracle`'s private
    `apply_workTapes_eq_of_ne` (line 304 at the campaign tip), the natural one to harvest.
- **Members on `Cfg.InWindow`** (lines at the campaign tip):
  - `Complexity.ExpBFS.inWin_mono` and `inWin_stepWith` (`SpaceComplexity/ExpBFS/Radius`, lines
    63 and 70; Hydroxyi's): the monotonicity, and one choice step from radius `s` into `s + 1`;
  - the window half of `Complexity.Codec.boundary_iff` (`SpaceComplexity/Codec/Step`, line 195;
    Hydroxyi's): once the two boundary cells are read as head conditions, `apply_iff`;
  - `codec_step_blank` (private, `ClassPSPACE/TQBF`, line 1505; the campaign's): the tape half at
    the same radius for one deterministic step;
  - `xr_window_stepWith` (private, `ClassNP/ExhaustiveReplay`, line 67; the campaign's):
    `inWin_stepWith` for any machine, with `Cfg.InWindow`'s two clauses written out (its output
    bound is outside the kind).
- **Members over other window shapes** (the widening; all the campaign's):
  - `Turing.FinTM.source_bounds` (`TuringMachine/Sweep`, line 359): the interval `[-t, t]`, its
    one-step case inline;
  - `Turing.OracleTM.step_radius` (`TuringMachine/Oracle`, line 346): a per-tape radius, one
    oracle step, through the private tape half above;
  - `dgWindow_step` (private, `TuringMachine/Robustness/SingleTape`, line 1933): the window part of
    a grown interval (its visited, history and size fields are outside the kind);
  - `emCall_track_support` with `emCall_track_extent` (private, `TuringMachine/Build/Loop`, lines
    3316 and 3294): the visited interval of a source run, its step inline.
- **Disposition:** the dedup window (12.2c): publish the tape half, then re-prove the members from
  the canonical statements or re-point their uses; a member over another window shape keeps its
  own statement and cites the canonical ones for its step. Eight of the members re-prove the tape
  half.

Census (members over **all source declarations**, public and private, anonymous instances
included, as `devtools/seyoon/declfreeze.py` counts them at #196's repair `b1b5199b`; corrected
by gate 96's round-2 minor 1, which found the style lint's count, without the seven anonymous
private instances, used before): `Build/CfgRecord` 2 of 137 (1.5%; the canonical pair), 3 of 137
(2.2%) with RO-1's `recordStep_runFrom_one`; `ExpBFS/Radius` 2 of 27 (7.4%) for WS-1, and **3 of
27 (11.1%) cumulatively** with CE-1's `coreSum_eq_of_code_eq`; `Codec/Step` 1 of 30 (3.3%); one
member each in `TQBF`, `ExhaustiveReplay`, `Sweep`, `Oracle` (`step_radius`; its private
`apply_workTapes_eq_of_ne` is the tape half's harvest source, not a copy) and
`Robustness/SingleTape`, and two declarations in `Build/Loop`. The one-fifth rule is not
reached.

**WL-1, a `WalkLe` equation in a consumer file** (gate 96, minor 3's residue; recorded
2026-11-05). `Complexity.LogProg.ISCount.walkLe_succ_iff` (`Logspace/ISCountMath`, line 120),
the last-edge form
`WalkLe R K (j + 1) c t ↔ WalkLe R K j c t ∨ ∃ w, WalkLe R K j c w ∧ R w t ∧ t < K`,
is a fact about `Complexity.WalkLe` (`Logspace/PathWalk`) that lives in a consumer file and
namespace, and its proof unfolds `WalkLe` by `simp only [WalkLe]`, a cross-file unfolding.
Since #196's repair (`b1b5199b`) `SavitchARM/Reach` no longer uses it: `chain_of_walkLe` reads
walks at the front through the new `Complexity.walkLe_succ_iff_head` (`PathWalk`, `Iff.rfl`),
and `Reach` imports `PathWalk` instead of `ISCountMath`. Its remaining uses are in
`ISCountMath`'s own `mem_succ_iff`. Not a copy. **Disposition:** the dedup window (12.2c): move
it beside `WalkLe` in `PathWalk`, or re-prove it there from `walkLe_succ_iff_head` without
unfolding, and cite it from `ISCountMath`. Both files are Hydroxyi's.

**WC-1, a window-run closure lemma (optional)** (gate 96, note 10; recorded 2026-11-05).
`Complexity.ExpBFS.winRun_of_card_eq` (`ExpBFS/Radius`) and the induction inside
`Complexity.LogProg.SavitchARM.mem_iff_reach_of_noEdge` (`SavitchARM/Window`) share about ten
lines of one skeleton: extend a window run by `WinRun.snoc`, then finish with `rcode_iff` and
`mem_acceptLang`. The closing steps differ: a shared pattern, not a copy. The induction also
shows more than it states: under `NoEdge`, every word is a window run. **Disposition
(optional):** the dedup window (12.2c): one closure lemma, "if every one-step extension of a
window run stays in the window, every word is a window run", from which `winRun_of_card_eq` and
a public `winRun_of_noEdge` both follow.

**QL-X1, an idiom exclusion: the query layout** (gate 96, note 11; ruled by the user,
2026-11-05). `SavitchARM/Window`'s `NoEdge` reproduces 85% of `SavitchARM/Recursion`'s `Rel` on
the v3 screen. The shared text is the query layout
`pairEncode x (pairEncode (bits u) … (bits s))`, through which each predicate reads a code
language or an oracle answer; `NoEdge` restates none of `Rel`'s meaning. **Ruled (user,
2026-11-05): an idiom**, as with NF-X1's. **Disposition:** excluded; not counted.

**CQ-1, codec-level query predicates** (gate 96, note 11; opened by the user, 2026-11-05, as a
12.2c item). The queries "`⟨x, ⟨bits u, bits s⟩⟩` is in `initLang N`" (and likewise for
`acceptLang N` and `edgeLang N`) are spelled out wherever they are used: in
`Complexity.LogProg.SavitchARM`'s `mem_iff_reach` and `NoEdge`, and in the deepening's block-fit
lemmas (the design's `BlockFit` probe: `fit_initO`, `fit_edgeO`, `fit_accO`, `fit_edge_block`).
`Logspace/ISCountGenRadius` names two of them as public `abbrev`s in a consumer file,
`ISGen.InitM` and `ISGen.AccM`, with no `_iff` lemmas. **Disposition:** the dedup window
(12.2c): a `def` per query, each with its `_iff` lemma, beside `initLang`, `acceptLang` and
`edgeLang` (`SpaceComplexity/Codec/Langs`), replacing `ISGen`'s `InitM` and `AccM` and serving
`mem_iff_reach`, `NoEdge` and the fit lemmas alike. `Codec/Langs` and `ISCountGenRadius` are
Hydroxyi's: interface design in their files.

**RP-1, definitional reads that #196's equations can replace** (gate 96, the round-2 shape
search; recorded 2026-11-05; not duplication). #196 publishes `Iff.rfl` equations for `WalkLe`,
`StepRel`, `RCode`, `WinRun`, `Rel`, `InitO` and `AccO`. Colleagues' files read these definitions
by unfolding or by definitional equality: `WalkLe` in `Logspace/ISCountGenWalk` (83–105),
`PathWalkMachine` (429–439) and `ISCountMath` (124); `StepRel` in `ExpBFS/Radius` (167),
`Logspace/PathHard` (232) and `Randomized/BPLInPCount` (119); `RCode` in `ExpBFS/Main` (98–104)
and `ISCountGenRadius` (88–92); `Rel`, `InitO` and `AccO` in `SavitchARM/Correct` (55–71); lines
at the campaign tip. **Disposition:** the dedup window (12.2c): re-point them to the equations.
Not counted.

**CE-1, equal codes of window configurations, copied** (found 2026-11-05 by gate 96's round-2
screen; **acknowledged by the user for 12.2c, 2026-11-05**). `coreSum_eq_of_code_eq` (equal
radius-`s` codes of two configurations in the radius-`s` window give equal vertices) is public, with
the same statement and the same one-line proof through `coreSum_eq_of_cfgWord_eq`, in
`SpaceComplexity/ExpBFS/Radius` (`Complexity.ExpBFS`, line 126 at the campaign tip) and in
`Randomized/BPLInPCount` (`Randomized.BPLInP`, line 106). Both files are Hydroxyi's, and the copy
predates #196. **Disposition:** the dedup window (12.2c): keep `ExpBFS`'s and re-point
`BPLInPCount`'s uses. Census: one declaration in each file.

**ZP-1, the zone row's precondition under a change of state** (#197, G5's consumer API; gate 97,
minor 5; ruled by the user, 2026-11-05). `Turing.zoneRowPre` (`Build/ZoneRebalance`) reads only
the work tapes and work tape `0`'s head, so it holds of a configuration exactly when it holds
after the state is renamed or rebound. No public lemma said so. `Build/ZoneStep` re-derived it
privately (`zs_rowPre_mapState`); G5's controller needs it too (its phase host starts a phase at
`d.mapState (fun _ => s₀)` and returns `post.bindState (red p)`); and `ZoneRebalance` proves it
inline twelve times, unfolding `zoneRowPre` with `funext_iff`, `Cfg.mapState_workTapes` and
`Cfg.mapState_workTapePos`. That is legal in the definition's home, so there is no rule-10 issue.
- **Ruled (user, 2026-11-05): publish** `zoneRowPre_congr` (across state types: equal work tapes
  and equal tape-`0` heads give the same precondition, which covers `mapState` and `bindState`)
  and its corollary `zoneRowPre_mapState_iff`, beside `zoneRowPre`. Done on #197's head
  `20e7fc75`; `ZoneStep` cites them, and its private copy is gone.
- **The twelve inline sites are re-pointed in the 12.2c window** (the same ruling): lines 831,
  884, 906, 1239, 2275, 2301, 2362, 3330, 3354, 3432, 3512 and 3539 at #197's original head
  `0a1b64d5` (each 22 lines lower at `20e7fc75`), one in each of `zr_rightSeekBack_post`,
  `zr_rightSeekBack_ruler_pre`, `zr_rightRuler_pre`, `zr_rightPass_pre`, `zr_rightReturn_pre`,
  `zr_rightReturn_post`, `zr_rightReturn_bounds`, `zr_rightLeft_pre`, `zr_rightLeft_post`,
  `zr_rightLeft_fields`, `zr_extend_pre` and `zr_extend_fields`.
- **Not RN-1, by kind.** RN-1's fact is a configuration equation (`Cfg.mapState_eq_of_fields`: a
  renamed configuration equals any configuration with its data fields and the renamed state),
  and its family is the five-line `Cfg.ext`/`Cfg.mapState_*` block. These twelve prove one
  predicate's invariance under a change of state, with no `Cfg.ext` and no configuration
  equation, so they are this 12.2c item, with `zoneRowPre_congr` and `zoneRowPre_mapState_iff`
  as its canonical statements. (Gate 97's pre-dispatch sweep, `evidence/sweep/README.md`, called
  `zs_rowPre_mapState` "RN-1's kind"; by RN-1's scope it belongs here.)
- **G5 (#211, gate 102; the review's F4):** `TwoTapes` does not cite the pair. Each phase starts at
  a configuration built at the phase's own state type (`tt_cfg_rowPre`), and each endpoint is
  converted by `tt_mapState_eq_cfg` through `zoneRowPre_iff` and RN-1's `Cfg.mapState_eq_of_fields`;
  nothing re-derives the state-independence. Not a member; the maintainer accepts the route.

Census (inline steps inside declarations, counted as RN-1's are; members over all declarations,
as the style lint counts them, at `20e7fc75`): `ZoneRebalance` 14 of 875 (1.6%: the twelve sites
and the canonical pair). Four of the twelve declarations also hold an RN-1 block
(`zr_rightSeekBack_post`, `zr_rightReturn_post`, `zr_rightLeft_post`, `zr_extend_fields`), so with
RN-1's 21 the file holds 31 of 875 (3.5%). The one-fifth rule is not reached.

Any new copy in a future delivery enters through the per-delivery ledger
and the one-fifth escalation rule of `workflow.md` §4.

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/freeze/declfreeze-TwoTapes.txt =====

public before/after: 2 2 private before/after: 0 102
public added: []
public removed: []
authorized body change: Turing.FinTM.two_work_tapes_run
private removed: []
private added: ['Turing.FinTM.tt_D', 'Turing.FinTM.tt_D_inv', 'Turing.FinTM.tt_D_level', 'Turing.FinTM.tt_D_succ', 'Turing.FinTM.tt_Dtr', 'Turing.FinTM.tt_Dtr_inv', 'Turing.FinTM.tt_Dtr_level_mono', 'Turing.FinTM.tt_Dtr_other', 'Turing.FinTM.tt_Dtr_own', 'Turing.FinTM.tt_Fam', 'Turing.FinTM.tt_HS', 'Turing.FinTM.tt_HS_init', 'Turing.FinTM.tt_I', 'Turing.FinTM.tt_LeafSt', 'Turing.FinTM.tt_Mf', 'Turing.FinTM.tt_Ph', 'Turing.FinTM.tt_T', 'Turing.FinTM.tt_T_ge', 'Turing.FinTM.tt_act', 'Turing.FinTM.tt_c', 'Turing.FinTM.tt_card_le_of_gap', 'Turing.FinTM.tt_cfg', 'Turing.FinTM.tt_cfg0', 'Turing.FinTM.tt_cfg_mapState', 'Turing.FinTM.tt_cfg_rowPre', 'Turing.FinTM.tt_converse', 'Turing.FinTM.tt_cost', 'Turing.FinTM.tt_count', 'Turing.FinTM.tt_cs', 'Turing.FinTM.tt_cs_halt', 'Turing.FinTM.tt_cs_round', 'Turing.FinTM.tt_cs_run', 'Turing.FinTM.tt_cs_start', 'Turing.FinTM.tt_decodeIn', 'Turing.FinTM.tt_dir', 'Turing.FinTM.tt_forward_run', 'Turing.FinTM.tt_frame', 'Turing.FinTM.tt_full', 'Turing.FinTM.tt_fullD', 'Turing.FinTM.tt_full_empty', 'Turing.FinTM.tt_full_extend', 'Turing.FinTM.tt_full_homeWrite', 'Turing.FinTM.tt_full_pre_false', 'Turing.FinTM.tt_full_pre_true', 'Turing.FinTM.tt_full_rebalance_false', 'Turing.FinTM.tt_full_rebalance_true', 'Turing.FinTM.tt_homeData', 'Turing.FinTM.tt_homeData_inv', 'Turing.FinTM.tt_homeNew', 'Turing.FinTM.tt_homeRead', 'Turing.FinTM.tt_idx', 'Turing.FinTM.tt_idxA', 'Turing.FinTM.tt_idxR', 'Turing.FinTM.tt_idxR_le', 'Turing.FinTM.tt_inputSymbol', 'Turing.FinTM.tt_ipOf', 'Turing.FinTM.tt_leafTM', 'Turing.FinTM.tt_leafTM_tr_moves', 'Turing.FinTM.tt_leafTM_tr_workTapes_of_ne', 'Turing.FinTM.tt_leafTr', 'Turing.FinTM.tt_leaf_step', 'Turing.FinTM.tt_mapState_eq_cfg', 'Turing.FinTM.tt_moveInputPos_val', 'Turing.FinTM.tt_moves', 'Turing.FinTM.tt_next', 'Turing.FinTM.tt_next_ne', 'Turing.FinTM.tt_orbit_rsum', 'Turing.FinTM.tt_phDec', 'Turing.FinTM.tt_phFin', 'Turing.FinTM.tt_phase_seg', 'Turing.FinTM.tt_red', 'Turing.FinTM.tt_red_track_neg', 'Turing.FinTM.tt_red_track_pos', 'Turing.FinTM.tt_rep', 'Turing.FinTM.tt_rep_home', 'Turing.FinTM.tt_round', 'Turing.FinTM.tt_roundData', 'Turing.FinTM.tt_round_disp', 'Turing.FinTM.tt_round_inv', 'Turing.FinTM.tt_round_rsum', 'Turing.FinTM.tt_route', 'Turing.FinTM.tt_rsum', 'Turing.FinTM.tt_rsum_extend', 'Turing.FinTM.tt_rsum_homeWrite', 'Turing.FinTM.tt_rsum_low', 'Turing.FinTM.tt_rsum_rebalance_false', 'Turing.FinTM.tt_rsum_rebalance_true', 'Turing.FinTM.tt_rsum_succ', 'Turing.FinTM.tt_shift', 'Turing.FinTM.tt_shift_dir', 'Turing.FinTM.tt_stAt', 'Turing.FinTM.tt_tape_rebalance', 'Turing.FinTM.tt_trackData', 'Turing.FinTM.tt_trackStep_inv', 'Turing.FinTM.tt_trackStep_rsum', 'Turing.FinTM.tt_trackTime', 'Turing.FinTM.tt_track_seg', 'Turing.FinTM.tt_tracks_seg', 'Turing.FinTM.tt_zero_tapes', 'Turing.FinTM.tt_τ', 'Turing.FinTM.tt_τ_le', 'Turing.FinTM.tt_τ_of_lt']
private changed: []

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/freeze/declfreeze-r1-to-head.txt =====

public before/after: 2 2 private before/after: 102 102
public added: []
public removed: []
authorized body change: Turing.FinTM.two_work_tapes_run
private removed: []
private added: []
private changed: ['Turing.FinTM.tt_forward_run']

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/lint/campaign-head.txt =====

WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  13241 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  9 public def(s) without a lemma beside them (check 8): catalogTrace, inputMoveAction, mealyRun, scanCarry, scanFold, scanKeep, scanMap, scanShift, tapeAction
WARN  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                5730 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1487 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1 public def(s) without a lemma beside them (check 8): roundStop
WARN  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean            1 public def(s) without a lemma beside them (check 8): Contract.liftSymbols
WARN  TCSlib/Complexity/TuringMachine/Build/Convention.lean               4 public def(s) without a lemma beside them (check 8): solveSplit, solveSplitWith, splitAtLastTrue, unaryTokenSplit
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2259 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2 public def(s) without a lemma beside them (check 8): counterLoopDecExit, counterLoopRedirect
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1170 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1 public def(s) without a lemma beside them (check 8): Cfg.select
WARN  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            1 public def(s) without a lemma beside them (check 8): SafeRun
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1309 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1 public def(s) without a lemma beside them (check 8): RulerAt
WARN  TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean       1592 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5294 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     2 public def(s) without a lemma beside them (check 8): callEntry, callExit
WARN  TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean              11 public def(s) without a lemma beside them (check 8): FinNDTM.clockHost, aI, bootCfg, capPush, clockTr, emitTo, hostTM, runCfg, sI, tapeAfter, yI
WARN  TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean           1 public def(s) without a lemma beside them (check 8): ClockReady
WARN  TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean            6 public def(s) without a lemma beside them (check 8): AgreeShift, coinBranchAct, coinBranchAct, coinBranchCfg, coinBranchCfg, mapOutputCfg
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   2057 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   3 public def(s) without a lemma beside them (check 8): GuessRunPhase.State, guessRunPhases, guessRunRed
WARN  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               1 public def(s) without a lemma beside them (check 8): answerAction
WARN  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean                2608 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7023 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              6136 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              4 public def(s) without a lemma beside them (check 8): TableAt, TableWF, recordTemplate, tableFields
WARN  TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean               1814 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                3533 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                6 public def(s) without a lemma beside them (check 8): SeekPh, SkipPh, afterTag, recordFinTM, roundFinTM, succFieldCfg
WARN  TCSlib/Complexity/TuringMachine/Build/StepClock.lean                1205 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean                1361 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 4 public def(s) without a lemma beside them (check 8): captureAction, captureCfg, emitAction, emitCfg
WARN  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1580 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            15414 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            2 public def(s) without a lemma beside them (check 8): zoneRowHi, zoneRowLo
WARN  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     5 public def(s) without a lemma beside them (check 8): codeScan, codeSkipTable2, codeSkipWork, oneTapeFormat, workPair
WARN  TCSlib/Complexity/TuringMachine/CodeParser.lean                     5 public def(s) without a lemma beside them (check 8): codeFallback, codeSkipAction, codeSkipFin, codeSkipPair, codeSkipState
WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  9124 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  3 public def(s) without a lemma beside them (check 8): MachineFormat.toFinTM, codeSkipTableK, oneTapeMachineFormat
WARN  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     1 public def(s) without a lemma beside them (check 8): Code2TM.toFinTM
WARN  TCSlib/Complexity/TuringMachine/CounterProg.lean                    5 public def(s) without a lemma beside them (check 8): act, ctl, init, toTM, tr
WARN  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               1 public def(s) without a lemma beside them (check 8): shiftInput
WARN  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 5 public def(s) without a lemma beside them (check 8): LinE.val, MOp.exec, bitsOps, linOps, tmplInstr
WARN  TCSlib/Complexity/TuringMachine/Encoding.lean                       2 public def(s) without a lemma beside them (check 8): CodeTM.serialize, actionBits
WARN  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean                1413 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/NDCodes.lean                        1 public def(s) without a lemma beside them (check 8): CodeNDTM.serialize
WARN  TCSlib/Complexity/TuringMachine/Oracle.lean                         4 public def(s) without a lemma beside them (check 8): Action.extend, initCfg, plainEmptyOracle, queryTapeIdx
WARN  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                1 public def(s) without a lemma beside them (check 8): queriesAlong
WARN  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   2 public def(s) without a lemma beside them (check 8): ComputesInTime, DecidesInTime
WARN  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         6 public def(s) without a lemma beside them (check 8): AcceptsWithin, DecidesInTime, FinOracleTM.toFinOracleNDTM, HaltsWithin, OracleNDTM.fixChoice, initCfg
WARN  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       1 public def(s) without a lemma beside them (check 8): NonnegativeHeads
WARN  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  7 public def(s) without a lemma beside them (check 8): blankPayload, clockTape, dataCell, laneCfg, obliviousDataInit, obliviousVisit, sourceWrittenPayload
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   5 public def(s) without a lemma beside them (check 8): Oblivious, clockBit, nextThird, oblAction, oblEmbed
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1 public def(s) without a lemma beside them (check 8): setupWrite
WARN  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean            2460 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     1212 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/Simulation.lean                     4 public def(s) without a lemma beside them (check 8): emitAction, leftAction, rightAction, virtualNextTag
WARN  TCSlib/Complexity/TuringMachine/Sweep.lean                          2 public def(s) without a lemma beside them (check 8): indexedVisit, sweepAct
WARN  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      1 public def(s) without a lemma beside them (check 8): wrT
WARN  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 1 public def(s) without a lemma beside them (check 8): universalBlockBound
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           14 public def(s) without a lemma beside them (check 8): universalActionBits, universalAdmin, universalEvalCfg, universalFour, universalInterpreter, universalNextOnes, universalRecordBits, universalRecordIndex, universalRecords, universalSign, universalSimulationCfg, universalSkipDone, universalStartupBound, universalWrite
WARN  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2873 lines > 1000: policy requires a split or a recorded justification (escalation/decision log)
WARN  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2 public def(s) without a lemma beside them (check 8): EffectiveCodeK.ofSerialize, EffectiveCodeK.toFinTM
WARN  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               3 public def(s) without a lemma beside them (check 8): universalCaptureCfg, universalCapturedCfg, universalInputPos
INFO  TCSlib/Complexity/TuringMachine/BufferWords.lean                    118 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Catalog.lean                  13241 lines; 113 public / 392 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean                904 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/CertShell.lean                904 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean                5730 lines; 24 public / 106 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean           1487 lines; 92 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Catalog.lean         562 lines; 27 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Counter.lean         134 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Embed.lean           130 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean            84 lines; 1 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean            840 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean            840 lines; 15 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Contract.lean                 62 lines; 0 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Convention.lean               252 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean              2259 lines; 59 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Embed.lean                    1170 lines; 32 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean             909 lines; 1 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean            326 lines; 18 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputCall.lean                535 lines; 2 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputDevice.lean              1309 lines; 16 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputLength.lean              571 lines; 1 public / 11 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputRewind.lean              201 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InputWindow.lean              438 lines; 1 public / 16 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/InterpreterStartup.lean       1592 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Loop.lean                     5294 lines; 21 public / 183 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean              598 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean           393 lines; 23 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean            379 lines; 24 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/NDHost.lean                   2057 lines; 56 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleCall.lean               182 lines; 6 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/OracleSim.lean                2608 lines; 13 public / 87 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Primitives.lean               7023 lines; 49 public / 236 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/RecordTable.lean              6136 lines; 29 public / 100 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Rewind.lean                   223 lines; 3 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     666 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Scan.lean                     666 lines; 9 public / 15 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     935 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Seam.lean                     935 lines; 26 public / 8 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/SeamLayout.lean               1814 lines; 1 public / 35 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlock.lean                3533 lines; 64 public / 71 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean         565 lines; 2 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepBlockLoop.lean            511 lines; 5 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/StepClock.lean                1205 lines; 9 public / 33 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean             543 lines; 20 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WindowRun.lean                1361 lines; 10 public / 25 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/WordTests.lean                136 lines; 4 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 806 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/Wrappers.lean                 806 lines; 14 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/Zone.lean                     1580 lines; 87 public / 12 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean            15414 lines; 25 public / 852 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean                 326 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Build/ZoneTape.lean                 568 lines; 48 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CfgFacts.lean                       119 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/ChoiceReplay.lean                   153 lines; 3 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/ChoiceWords.lean                    118 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeFormat.lean                     595 lines; 47 public / 3 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeParser.lean                     487 lines; 44 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CodeSimulator.lean                  9124 lines; 12 public / 196 private declarations
INFO  TCSlib/Complexity/TuringMachine/Codes2Tape.lean                     355 lines; 11 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    829 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Composition.lean                    829 lines; 19 public / 7 private declarations
INFO  TCSlib/Complexity/TuringMachine/Configuration.lean                  278 lines; 21 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProg.lean                    562 lines; 28 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgInput.lean               93 lines; 5 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/CounterProgRun.lean                 448 lines; 35 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Deterministic.lean                  535 lines; 42 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       797 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Encoding.lean                       797 lines; 55 public / 9 private declarations
INFO  TCSlib/Complexity/TuringMachine/Finite.lean                         485 lines; 26 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/MathlibBridge.lean                  1172 lines; 21 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodeSimulator.lean                1413 lines; 3 public / 41 private declarations
INFO  TCSlib/Complexity/TuringMachine/NDCodes.lean                        277 lines; 7 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               642 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Nondeterministic.lean               642 lines; 28 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/NondeterministicSpace.lean          194 lines; 6 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         704 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Oracle.lean                         704 lines; 42 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleAgreement.lean                375 lines; 9 public / 5 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleFinite.lean                   149 lines; 7 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean         408 lines; 25 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   937 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean   937 lines; 3 public / 60 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean       464 lines; 2 public / 37 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean           1147 lines; 1 public / 38 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean  1127 lines; 47 public / 42 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousLedger.lean     219 lines; 4 public / 2 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSchedule.lean   688 lines; 19 public / 20 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean      1102 lines; 8 public / 59 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean          2319 lines; 4 public / 96 private declarations
INFO  TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean            2460 lines; 2 public / 102 private declarations
INFO  TCSlib/Complexity/TuringMachine/SelfUniversal.lean                  159 lines; 2 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Simulation.lean                     1212 lines; 62 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/StateRenaming.lean                  230 lines; 9 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Sweep.lean                          392 lines; 22 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/SymbolLift.lean                     478 lines; 32 public / 1 private declarations
INFO  TCSlib/Complexity/TuringMachine/UnaryTape.lean                      84 lines; 8 public / 0 private declarations
INFO  TCSlib/Complexity/TuringMachine/Universal.lean                      2884 lines; 4 public / 129 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalBlock.lean                 794 lines; 6 public / 17 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean           1027 lines; 37 public / 13 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalK.lean                     2873 lines; 12 public / 67 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               638 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/UniversalStartup.lean               638 lines; 16 public / 18 private declarations
INFO  TCSlib/Complexity/TuringMachine/UniversalTlogT.lean                 84 lines; 1 public / 0 private declarations

style_lint: 0 FAIL, 72 WARN over 92 files

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/lint/policy-head.txt =====


1 findings in 1 files
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean: 2461 lines (> 1000, must split)

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/merged-tree/down-lg7.txt =====

TCSlib/Complexity/TuringMachine/Robustness/TwoTapes
TCSlib/Complexity/TuringMachine/UniversalTlogT
TCSlib/Complexity/TuringMachine

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/merged-tree/replay-lg7-static.txt =====

modules 3, mismatches 0, static total 0

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/merged-tree/replay-lg7.log =====

# replay-lg7 at e7e78aaf: #211, gate 102 round 2 (3 modules), fresh .oleans into oleans-lg7
TCSlib/Complexity/TuringMachine/Robustness/TwoTapes exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine/UniversalTlogT exit=0 errors=0 sorry=0
TCSlib/Complexity/TuringMachine exit=0 errors=0 sorry=0
# modules=3 failed=0

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/merged-tree/replay-lg7.sh =====

#!/usr/bin/env bash
# Replay lg7 (#211, gate 102 round 2; branch lean/u2s-g5-landing, stacked on the campaign after #209): its downstream closure (3 modules),
# fresh .oleans into oleans-lg7, a copy of oleans-lnth, via scripts/lean_check_tree.sh. The root TCSlib
# module is not listed (replay rule). The precheck pins the changed files' blobs.
S=/home/user/tcslib-scratch
WT="$S/wt-191"
LIST="/home/user/tcslib-scratch/fills/replay/down-lg7.txt"
LOG="$S/fills/replay/replay-lg7.log"
PINS="TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean:e1ef486ece9ce00d5cc3b696a36ffc54e1fbb456"
[ -d "$WT/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib" ] || { echo "precheck: $WT/.lake/packages has no Mathlib build; nothing copied" >&2; exit 2; }
git -C "$WT" fetch -q origin 2>/dev/null
[ "$(git -C "$WT" rev-parse HEAD)" = "$(git -C "$WT" rev-parse origin/lean/u2s-g5-landing 2>/dev/null)" ] || { echo "precheck: $WT is not at the pushed PR head; nothing copied" >&2; exit 2; }
[ -z "$(git -C "$WT" status --porcelain --untracked-files=no)" ] || { echo "precheck: $WT has local changes; nothing copied" >&2; exit 2; }
git -C "$WT" merge-base --is-ancestor 64a9925a8a00152144a4f324a6aa266b1aab406f HEAD || { echo "precheck: the head must contain the campaign after #209; nothing copied" >&2; exit 2; }
[ "$(git -C "$WT" diff --name-only 64a9925a8a00152144a4f324a6aa266b1aab406f HEAD -- '*.lean' | sort)" = "$(printf '%s\n' "$PINS" | cut -d: -f1 | sort)" ] || { echo "precheck: the Lean diff from the campaign after #209 must be exactly the pinned files; nothing copied" >&2; exit 2; }
while IFS=: read -r f b; do
  [ "$(git -C "$WT" rev-parse "HEAD:$f")" = "$b" ] || { echo "precheck: $f is not the checked blob; nothing copied" >&2; exit 2; }
done <<< "$PINS"
tail -1 "/home/user/tcslib-scratch/fills/replay/replay-lnth.log" 2>/dev/null | grep -qx "# modules=[0-9]* failed=0" || { echo "precheck: the previous replay must have passed; nothing copied" >&2; exit 2; }
[ "$(wc -l < "$LIST" | tr -d ' ')" = "3" ] || { echo "precheck: the replay list must have 3 modules; nothing copied" >&2; exit 2; }
grep -qx "TCSlib" "$LIST" && { echo "precheck: the replay list must not contain the root TCSlib; nothing copied" >&2; exit 2; }
[ -d "$S/oleans-lg7" ] && { echo "precheck: $S/oleans-lg7 already exists; remove it for a fresh copy" >&2; exit 2; }
[ -d "$S/oleans-lnth" ] || { echo "precheck: oleans-lnth is missing; nothing copied" >&2; exit 2; }
cp -R "$S/oleans-lnth" "$S/oleans-lg7" || exit 1
cd "$WT" || exit 1
{ echo "# replay-lg7 at $(git rev-parse --short HEAD): #211, gate 102 round 2 ($(wc -l < "$LIST" | tr -d ' ') modules), fresh .oleans into oleans-lg7"
  n=0; f=0
  while read -r m; do
    n=$((n+1))
    out=$(TCSLIB_OLEANS=$S/oleans-lg7 nice -n 10 bash scripts/lean_check_tree.sh "$m" 2>&1); st=$?
    e=$(printf '%s\n' "$out" | grep -c "error")
    echo "$m exit=$st errors=$e sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")"
    [ $st -ne 0 ] && { f=$((f+1)); printf '%s\n' "$out" | grep error | head -3 | sed "s#$PWD/##g"; }
  done < "$LIST"
  echo "# modules=$n failed=$f"
} > "$LOG" 2>&1
python3 -I "$S/api/staticsorry.py" "$WT" "$LOG" > "${LOG%.log}-static.txt"; sst=$?
tail -n 6 "$LOG"
tail -n 1 "${LOG%.log}-static.txt"
# the exit status: nonzero unless every listed module passed and the static check found no mismatch
tail -1 "$LOG" | grep -qx "# modules=3 failed=0" || { echo "replay: a module failed, or the count is not 3" >&2; exit 1; }
[ $sst -eq 0 ] && tail -1 "${LOG%.log}-static.txt" | grep -q "mismatches 0," || { echo "replay: the static sorry check failed" >&2; exit 1; }
exit 0

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/round2-edits.diff =====

diff --git a/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean b/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
index 87fe5c9d..e1ef486e 100644
--- a/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
+++ b/TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
@@ -1599,8 +1599,7 @@ private theorem tt_forward_run (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk
   | zero =>
     exfalso
     have h0 : (M.tm.runFrom (M.tm.initCfg x) 0).state = none := heq ▸ hs
-    rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq, Cfg.init_state] at h0
-    cases h0
+    exact not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)
   | succ s =>
     have hl : ∀ r < s + 1, (tt_c M x r).state ≠ none := fun r hr => hlive r hr
     refine ⟨s + 1, hu, Nat.le_add_left 1 s, hl, ?_⟩
@@ -2418,9 +2417,11 @@ the same input.
 **Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
 `M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
 `2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
-between neighbouring zones. Each zone is kept half full. A shift that empties or fills a zone `i`
-rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, and a zone `i`
-is rebalanced at most once every `2^(i-1)` simulated steps. Summing over the zones
+between neighbouring zones. Each side of a level is empty, half full or full, and the two sides
+of a level together always hold the same number of cells. A shift that empties or fills a zone `i`
+rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, restoring
+every level below `i` to half full, and a zone `i` is rebalanced at most once every `2^(i-1)`
+simulated steps. Summing over the zones
 `0, …, log₂ t + 1` that a run of `t` steps can rebalance gives `O(t log t)` steps in all. The
 converse holds because `M'` writes an output symbol exactly when `M` does, in the same order, and
 halts only when `M` halts. With no work tapes, `M` is run directly beside two idle tapes. -/

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/screen/pairdiff-vs-r1.txt =====

head pairs 840; union of earlier 840; new at head 0; earlier-only 0

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/screen/population.txt =====

TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean
TCSlib/Complexity/TuringMachine/Build/ZoneStep.lean
TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean
TCSlib/Complexity/TuringMachine/Build/ZoneTape.lean
TCSlib/Complexity/TuringMachine/Build/Zone.lean
TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean
TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean
TCSlib/Complexity/TuringMachine/Build/Seam.lean
TCSlib/Complexity/TuringMachine/Build/Embed.lean
TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean
TCSlib/Complexity/TuringMachine/CfgFacts.lean
TCSlib/Complexity/TuringMachine/StateRenaming.lean
TCSlib/Complexity/TuringMachine/Configuration.lean
TCSlib/Complexity/TuringMachine/Deterministic.lean
TCSlib/Complexity/TuringMachine/Finite.lean
TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean
TCSlib/Complexity/TuringMachine/UniversalTlogT.lean
TCSlib/Complexity/TuringMachine/Build/StepBlockForward.lean
TCSlib/Complexity/TuringMachine/Universal.lean
TCSlib/Complexity/TuringMachine/SymbolLift.lean
TCSlib/Complexity/TuringMachine/Build/Contract/Lift.lean
TCSlib/Complexity/TuringMachine/Simulation.lean

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/screen/screen-head.txt =====

declarations screened: 1277; copy pairs (target reproduces >= half of source): 840; reproduced text: 288,323 chars
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 135/135 = 100%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive: 62/62 = 100%
   AlphabetReduction.lean::alphabet_reduction_spaceUsed  reproduces  AlphabetReduction.lean::alphabet_reduction: 184/185 = 99%
   Zone.lean::zoneTrackTape_rebalance_right  reproduces  Zone.lean::zoneSide_rebalance_right: 266/269 = 99%
   Embed.lean::embedSilentRetTM  reproduces  Embed.lean::embedEmitRetTM: 215/219 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 132/135 = 98%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 132/135 = 98%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Eval_reads: 86/88 = 98%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_rightBoundary: 71/73 = 97%
   SingleTape.lean::sweepPos_move  reproduces  SingleTape.lean::dgPos_move: 67/69 = 97%
   Zone.lean::zoneShiftOut  reproduces  Zone.lean::zoneShiftIn: 314/324 = 97%
   Zone.lean::zoneSide_rebalance_right  reproduces  Zone.lean::zoneTrackTape_rebalance_right: 266/275 = 97%
   Embed.lean::embedEmitRetTM  reproduces  Embed.lean::embedSilentRetTM: 215/224 = 96%
   Zone.lean::zoneShiftIn  reproduces  Zone.lean::zoneShiftOut: 314/329 = 95%
   AlphabetReduction.lean::arTail_update  reproduces  AlphabetReduction.lean::arTape_update: 78/82 = 95%
   ZoneTape.lean::zoneOwner_sep  reproduces  ZoneTape.lean::zoneOwner_beyond: 105/111 = 95%
   Basic.lean::RoundContract  reproduces  Basic.lean::ReturnContract: 412/436 = 94%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Eval_reads: 83/88 = 94%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_right: 171/183 = 93%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_rightBoundary: 68/73 = 93%
   SingleTape.lean::dgPos_move  reproduces  SingleTape.lean::sweepPos_move: 67/72 = 93%
   Universal.lean::timedSix  reproduces  Universal.lean::timedFive: 78/84 = 93%
   SingleTape.lean::dg_sweep_reverse_prefix  reproduces  SingleTape.lean::dg_sweep_prefix: 232/250 = 93%
   Simulation.lean::rewind_heads  reproduces  Simulation.lean::timed_rewind: 395/435 = 91%
   Universal.lean::timed_universal_concrete  reproduces  Universal.lean::timed_universal: 384/424 = 91%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_initial_skip: 911/1008 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 121/135 = 90%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 121/135 = 90%
   ZoneTape.lean::zonedTape_right  reproduces  ZoneTape.lean::zonedTape_left: 171/191 = 90%
   SingleTape.lean::dg_sweep_prefix  reproduces  SingleTape.lean::dg_sweep_reverse_prefix: 232/261 = 89%
   TwoTapes.lean::tt_D_inv  reproduces  TwoTapes.lean::tt_D_succ: 109/123 = 89%
   Deterministic.lean::step  reproduces  Deterministic.lean::outputSymbol: 76/86 = 88%
   SingleTape.lean::dgSpan_generate_left  reproduces  SingleTape.lean::dgSpan_generate_right: 359/409 = 88%
   ZoneRebalance.lean::zr_fp8  reproduces  ZoneRebalance.lean::zr_fp6: 418/477 = 88%
   Deterministic.lean::outputSymbol  reproduces  Deterministic.lean::step: 76/87 = 87%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Universal.lean::timedCapture_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Universal.lean::timedFrame_run: 110/126 = 87%
   ZoneRebalance.lean::zr_out2Test_step  reproduces  ZoneRebalance.lean::zr_out1Test_step: 295/338 = 87%
   ZoneRebalance.lean::zr_fp6  reproduces  ZoneRebalance.lean::zr_fp8: 418/481 = 87%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_return_post: 400/461 = 87%
   TwoTapes.lean::tt_rsum_rebalance_false  reproduces  TwoTapes.lean::tt_rsum_rebalance_true: 867/1000 = 87%
   TwoTapes.lean::tt_cs_round  reproduces  TwoTapes.lean::tt_cs_halt: 551/636 = 87%
   TwoTapes.lean::tt_D  reproduces  TwoTapes.lean::tt_idxR: 84/97 = 87%
   Simulation.lean::bufferedFirstCfg_run  reproduces  Universal.lean::timedCapture_run: 146/169 = 86%
   Embed.lean::embedSilentCfg  reproduces  Embed.lean::embedEmitCfg: 165/192 = 86%
   ZoneRebalance.lean::zr_p2Body_back  reproduces  ZoneRebalance.lean::zr_p1Body_back: 91/106 = 86%
   ZoneRebalance.lean::zr_scanLoopContract  reproduces  ZoneRebalance.lean::zr_scanLoopPost: 120/140 = 86%
   ZoneRebalance.lean::zr_p4Arm  reproduces  ZoneRebalance.lean::zr_p3Arm: 188/220 = 85%
   Universal.lean::timedCapture_step  reproduces  Universal.lean::timedCapture_init: 271/318 = 85%
   ZoneRebalance.lean::zr_rightPass_bounds  reproduces  ZoneRebalance.lean::zr_rightPass_time: 568/667 = 85%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::endpoint_not_mem: 97/114 = 85%
   ZoneRebalance.lean::zr_p1Body_back  reproduces  ZoneRebalance.lean::zr_p2Body_back: 91/107 = 85%
   ZoneRebalance.lean::zr_pinTestContract  reproduces  ZoneRebalance.lean::zr_wordTestContract: 147/173 = 85%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq_positive  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch_positive: 62/73 = 85%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::segment_iff: 84/99 = 85%
   ZoneRebalance.lean::zr_mir_post  reproduces  ZoneRebalance.lean::zr_mir_mir: 200/236 = 85%
   ZoneRebalance.lean::zr_pinBack_step  reproduces  ZoneRebalance.lean::zr_pinSkip_step: 321/379 = 85%
   ZoneRebalance.lean::zr_p3Arm  reproduces  ZoneRebalance.lean::zr_p4Arm: 188/222 = 85%
   TwoTapes.lean::tt_rsum_rebalance_true  reproduces  TwoTapes.lean::tt_rsum_rebalance_false: 867/1026 = 85%
   Basic.lean::time_box  reproduces  Basic.lean::time_envelope: 123/146 = 84%
   TwoTapes.lean::tt_full_rebalance_true  reproduces  TwoTapes.lean::tt_full_rebalance_false: 966/1155 = 84%
   TwoTapes.lean::tt_full_pre_false  reproduces  TwoTapes.lean::tt_full_pre_true: 647/774 = 84%
   ZoneRebalance.lean::zr_fpRow  reproduces  ZoneRebalance.lean::zr_rowP0: 122/146 = 84%
   ZoneRebalance.lean::zr_rightLeftRow  reproduces  ZoneRebalance.lean::zr_rightPassRow: 71/85 = 84%
   TwoTapes.lean::tt_T  reproduces  TwoTapes.lean::tt_idxR: 81/97 = 84%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_return_time: 123/148 = 83%
   ZoneRebalance.lean::zr_fpRow  reproduces  ZoneRebalance.lean::zr_rowU: 103/124 = 83%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_inA1: 73/88 = 83%
   TwoTapes.lean::tt_full_pre_true  reproduces  TwoTapes.lean::tt_full_pre_false: 647/781 = 83%
   ZoneRebalance.lean::zr_rowInst  reproduces  ZoneRebalance.lean::zr_rowDec: 84/102 = 82%
   ZoneRebalance.lean::zr_inSeg_spec  reproduces  ZoneRebalance.lean::zr_prSeg_spec: 148/180 = 82%
   Basic.lean::hullLo  reproduces  Basic.lean::hullHi: 114/139 = 82%
   Basic.lean::hullHi  reproduces  Basic.lean::hullLo: 114/139 = 82%
   ZoneRebalance.lean::zr_shiftIn_off  reproduces  ZoneRebalance.lean::zr_shiftIn_zero: 133/163 = 82%
   ZoneRebalance.lean::zr_stk_pop  reproduces  ZoneRebalance.lean::zr_stk_push: 154/189 = 81%
   SingleTape.lean::sweep_init_block  reproduces  SingleTape.lean::sweep_grow_right_block: 428/526 = 81%
   SingleTape.lean::dg_end_with_growth  reproduces  SingleTape.lean::dg_end_without_growth: 371/456 = 81%
   ZoneRebalance.lean::zr_pinSkip_step  reproduces  ZoneRebalance.lean::zr_pinBack_step: 321/395 = 81%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_wordTest_wordAt: 195/240 = 81%
   ZoneRebalance.lean::zr_rightLeft_pre  reproduces  ZoneRebalance.lean::zr_extend_pre: 147/181 = 81%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_test_time: 82/101 = 81%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_return_post: 374/461 = 81%
   SingleTape.lean::sweep_turn_right  reproduces  SingleTape.lean::sweepRevCfg_write: 189/233 = 81%
   Simulation.lean::rightCfg_step  reproduces  Simulation.lean::leftCfg_step: 306/378 = 81%
   ZoneRebalance.lean::zr_inSeg_spec  reproduces  ZoneRebalance.lean::zr_retSeg_spec: 122/151 = 81%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_return_post: 372/461 = 81%
   ZoneRebalance.lean::zr_prSeg_spec  reproduces  ZoneRebalance.lean::zr_hmSeg_spec: 99/123 = 80%
   ZoneRebalance.lean::zr_halfCopyContract  reproduces  ZoneRebalance.lean::zr_rulerCopyContract: 66/82 = 80%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_outO1: 61/76 = 80%
   Simulation.lean::bufferedFirstCfg_init  reproduces  Universal.lean::timedCapture_init: 255/318 = 80%
   Embed.lean::embedSilent_step  reproduces  Embed.lean::embedEmit_step: 315/393 = 80%
   ZoneRebalance.lean::zr_shiftIn_zero  reproduces  ZoneRebalance.lean::zr_shiftIn_off: 133/166 = 80%
   ZoneRebalance.lean::zr_shortPin  reproduces  ZoneRebalance.lean::zr_rightPassRow: 68/85 = 80%
   TwoTapes.lean::tt_full_rebalance_false  reproduces  TwoTapes.lean::tt_full_rebalance_true: 966/1212 = 80%
   Simulation.lean::leftCfg_step  reproduces  Simulation.lean::rightCfg_step: 306/384 = 80%
   ZoneRebalance.lean::zr_decHost  reproduces  ZoneRebalance.lean::zr_finHost: 94/118 = 80%
   Universal.lean::timedCut_Interpreter_first  reproduces  Universal.lean::timedCut_Admin_apply: 210/264 = 80%
   ZoneRebalance.lean::zr_wordTestContract  reproduces  ZoneRebalance.lean::zr_pinTestContract: 147/185 = 79%
   ZoneRebalance.lean::zr_stk_push  reproduces  ZoneRebalance.lean::zr_stk_pop: 154/194 = 79%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedPrefix_penultimate: 318/401 = 79%
   ZoneRebalance.lean::zr_rightPass_time  reproduces  ZoneRebalance.lean::zr_body_time: 61/77 = 79%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_clock_separator: 236/298 = 79%
   Universal.lean::timedCapture_init  reproduces  Simulation.lean::bufferedFirstCfg_init: 255/322 = 79%
   ZoneRebalance.lean::zr_leftMove_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 133/168 = 79%
   Embed.lean::embedSilentRet_step  reproduces  Embed.lean::embedSilentRetTM_visitedByTapeHead: 106/134 = 79%
   ZoneRebalance.lean::zr_extend_pre  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 147/186 = 79%
   ZoneRebalance.lean::zr_rhome_iff  reproduces  ZoneRebalance.lean::zr_lhome_iff: 109/138 = 79%
   ZoneRebalance.lean::zr_lhome_iff  reproduces  ZoneRebalance.lean::zr_rhome_iff: 109/138 = 79%
   ZoneRebalance.lean::zr_pinClearContract  reproduces  ZoneRebalance.lean::zr_pinSkipContract: 101/128 = 79%
   ZoneRebalance.lean::zr_p1Hi  reproduces  ZoneRebalance.lean::zr_p1U: 71/90 = 79%
   ZoneRebalance.lean::zr_lcol  reproduces  ZoneRebalance.lean::zr_col_zone: 304/386 = 79%
   Configuration.lean::moveInputPos_neg_of_ne_left  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 85/108 = 79%
   ZoneRebalance.lean::zr_inTest_step  reproduces  ZoneRebalance.lean::zr_out1Test_step: 266/338 = 79%
   ZoneRebalance.lean::zr_p4Pass  reproduces  ZoneRebalance.lean::zr_p3Pass: 552/702 = 79%
   ZoneRebalance.lean::zr_p3Pass  reproduces  ZoneRebalance.lean::zr_p4Pass: 552/702 = 79%
   ZoneRebalance.lean::zr_rightReturn_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 110/140 = 79%
   ZoneRebalance.lean::zr_rightLeft_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 110/140 = 79%
   ZoneRebalance.lean::zr_extend_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 110/140 = 79%
   ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_return_post: 362/461 = 79%
   ZoneRebalance.lean::zr_lbPass  reproduces  ZoneRebalance.lean::zr_lbBack: 117/149 = 79%
   ZoneTape.lean::zonedTape_left_sep  reproduces  ZoneTape.lean::zonedTape_right_sep: 124/158 = 78%
   ZoneRebalance.lean::zr_woPass  reproduces  ZoneRebalance.lean::zr_woBack: 116/148 = 78%
   ZoneRebalance.lean::zr_return_bounds  reproduces  ZoneRebalance.lean::zr_return_time: 115/148 = 78%
   ZoneRebalance.lean::zr_pinSkipContract  reproduces  ZoneRebalance.lean::zr_pinClearContract: 101/130 = 78%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Frames.trans  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   Basic.lean::Cfg.SameOutside.keep_blank  reproduces  Basic.lean::traj_iff: 80/103 = 78%
   ZoneRebalance.lean::zr_prSeg_spec  reproduces  ZoneRebalance.lean::zr_retSeg_spec: 117/151 = 77%
   SingleTape.lean::dgSpan_generate_right  reproduces  SingleTape.lean::dgSpan_generate_left: 359/465 = 77%
   ZoneRebalance.lean::zr_return_post  reproduces  ZoneRebalance.lean::zr_return_time: 114/148 = 77%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_return_post: 355/461 = 77%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_return_post: 355/461 = 77%
   ZoneRebalance.lean::zr_outSeg_spec  reproduces  ZoneRebalance.lean::zr_inSeg_spec: 166/216 = 77%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_prSeg: 3531/4602 = 77%
   ZoneRebalance.lean::zr_scr_copy  reproduces  ZoneRebalance.lean::zr_scr_clear: 441/575 = 77%
   ZoneRebalance.lean::zr_goRoom  reproduces  ZoneRebalance.lean::zr_hmBr: 325/424 = 77%
   ZoneTape.lean::zonedTape_right_sep  reproduces  ZoneTape.lean::zonedTape_left_sep: 124/162 = 77%
   SingleTape.lean::sweepInput_read  reproduces  SingleTape.lean::dgInput_read: 189/247 = 77%
   SingleTape.lean::sweep_grow_left_block  reproduces  SingleTape.lean::sweep_init_block: 446/583 = 77%
   Universal.lean::timedFive  reproduces  Universal.lean::timedSix: 78/102 = 76%
   ZoneRebalance.lean::zr_p1U  reproduces  ZoneRebalance.lean::zr_p1Hi: 71/93 = 76%
   ZoneRebalance.lean::zr_finalLoopContract  reproduces  ZoneRebalance.lean::zr_shortLoopContract: 132/174 = 76%
   ZoneRebalance.lean::zr_p4Arm_step  reproduces  ZoneRebalance.lean::zr_woLead_step: 492/649 = 76%
   ZoneRebalance.lean::zr_rightLeft_post  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 141/186 = 76%
   Basic.lean::round_iff  reproduces  Basic.lean::segment_iff: 75/99 = 76%
   Embed.lean::embedEmitRet_step  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 87/115 = 76%
   Simulation.lean::rightCfg_apply  reproduces  Simulation.lean::leftCfg_apply: 142/188 = 76%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM: 148/196 = 76%
   Zone.lean::zoneMoveRight  reproduces  Zone.lean::zoneMoveLeft: 336/445 = 76%
   ZoneRebalance.lean::zr_prSeg  reproduces  ZoneRebalance.lean::zr_retSeg: 2194/2906 = 75%
   ZoneRebalance.lean::zr_test_post  reproduces  ZoneRebalance.lean::zr_test_time: 76/101 = 75%
   ZoneRebalance.lean::zr_dn_valid  reproduces  ZoneRebalance.lean::zr_rb_valid: 121/161 = 75%
   Zone.lean::zoneSide_shiftOutW  reproduces  Zone.lean::zoneSide_shiftInW: 296/394 = 75%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_return_post: 346/461 = 75%
   ZoneRebalance.lean::zr_p1Br_step  reproduces  ZoneRebalance.lean::zr_p2Br_step: 339/452 = 75%
   ZoneRebalance.lean::zr_shortPin_pre  reproduces  ZoneRebalance.lean::zr_cc_scratch: 158/211 = 75%
   Zone.lean::zoneMoveLeft  reproduces  Zone.lean::zoneMoveRight: 336/449 = 75%
   ZoneRebalance.lean::zr_twoSteps_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 139/186 = 75%
   ZoneRebalance.lean::zr_fp3  reproduces  ZoneRebalance.lean::zr_fp4: 150/201 = 75%
   ZoneRebalance.lean::zr_finHost  reproduces  ZoneRebalance.lean::zr_decHost: 94/126 = 75%
   ZoneRebalance.lean::zr_p2Pass  reproduces  ZoneRebalance.lean::zr_p1Pass: 504/676 = 75%
   ZoneRebalance.lean::zr_p2_facts  reproduces  ZoneRebalance.lean::zr_p1_facts: 102/137 = 74%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 125/168 = 74%
   CfgFacts.lean::Cfg.mapState_const_eq_mapState_sigma  reproduces  CfgFacts.lean::Cfg.mapState_eq_of_fields: 130/175 = 74%
   ZoneRebalance.lean::zr_fp8  reproduces  ZoneRebalance.lean::zr_fp4: 149/201 = 74%
   ZoneRebalance.lean::zr_fp6  reproduces  ZoneRebalance.lean::zr_fp4: 149/201 = 74%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timed_clock_back: 401/541 = 74%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 140/189 = 74%
   Simulation.lean::leftCfg_apply  reproduces  Simulation.lean::rightCfg_apply: 142/192 = 74%
   ZoneRebalance.lean::zr_p1Tau_le  reproduces  ZoneRebalance.lean::zr_rbTau_le: 99/134 = 74%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timed_output_back: 401/543 = 74%
   Basic.lean::segment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::safeSegment_iff  reproduces  Basic.lean::round_iff: 75/102 = 74%
   Basic.lean::endpoint_not_mem  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 97/132 = 73%
   ZoneRebalance.lean::zr_woBody_step  reproduces  ZoneRebalance.lean::zr_popEsc: 72/98 = 73%
   Embed.lean::embedEmit_step  reproduces  Embed.lean::embedSilent_step: 315/429 = 73%
   SingleTape.lean::sweep_grow_right_block  reproduces  SingleTape.lean::sweep_init_block: 428/583 = 73%
   Configuration.lean::moveInputPos_pos_of_ne_right  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 85/116 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead_frame: 204/279 = 73%
   ZoneRebalance.lean::zr_fpG1  reproduces  ZoneRebalance.lean::zr_p1Hi: 68/93 = 73%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Universal.lean::timedFrame_run: 92/126 = 73%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 235/322 = 73%
   Universal.lean::timedCut_Admin_apply  reproduces  Universal.lean::timedCut_Interpreter_first: 210/288 = 73%
   ZoneRebalance.lean::zr_extend_time_le  reproduces  ZoneRebalance.lean::zr_rightPass_time_le: 70/96 = 73%
   SingleTape.lean::dgStart  reproduces  SingleTape.lean::sweepStart: 148/203 = 73%
   Basic.lean::ReturnContract  reproduces  Basic.lean::RoundContract: 412/566 = 73%
   ZoneRebalance.lean::zr_hmTest_step  reproduces  ZoneRebalance.lean::zr_out1Test_step: 246/338 = 73%
   ZoneRebalance.lean::zr_hmZ_eq  reproduces  ZoneRebalance.lean::zr_hm_off: 269/370 = 73%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_unary: 911/1254 = 73%
   Universal.lean::timedCapture_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   Simulation.lean::bufferedFirstCfg_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 122/168 = 73%
   ZoneRebalance.lean::zr_shortPin_step  reproduces  ZoneRebalance.lean::zr_ccPin_step: 1031/1420 = 73%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_frame: 82/113 = 73%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_return_post: 334/461 = 72%
   ZoneRebalance.lean::zr_pair_pass  reproduces  ZoneRebalance.lean::zr_inPass_out: 92/127 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_max  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_spaceUsedByTape_le_add: 92/127 = 72%
   AlphabetReduction.lean::arWriteCfg  reproduces  AlphabetReduction.lean::arMoveCfg: 113/156 = 72%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_test_time: 73/101 = 72%
   ZoneRebalance.lean::zr_ccPin_step  reproduces  ZoneRebalance.lean::zr_shortPin_step: 1031/1427 = 72%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_body_post: 400/554 = 72%
   SingleTape.lean::sweepStart  reproduces  SingleTape.lean::dgStart: 148/205 = 72%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Universal.lean::timedCapture_run: 122/169 = 72%
   ZoneRebalance.lean::zr_shortLoopContract  reproduces  ZoneRebalance.lean::zr_finalLoopContract: 132/183 = 72%
   Zone.lean::zoneShiftIndex_nonempty  reproduces  Zone.lean::zoneShiftIndex_le: 80/111 = 72%
   ZoneRebalance.lean::zr_rightLeft_link  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 121/168 = 72%
   TwoTapes.lean::tt_orbit_rsum  reproduces  TwoTapes.lean::tt_T_ge: 90/125 = 72%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_hmSc2: 6479/8999 = 72%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_prSeg: 3312/4602 = 72%
   Universal.lean::timedBorrow_length  reproduces  Universal.lean::timedBorrow_fold: 64/89 = 72%
   Simulation.lean::rightAction  reproduces  Simulation.lean::leftAction: 69/96 = 72%
   Simulation.lean::leftAction  reproduces  Simulation.lean::rightAction: 69/96 = 72%
   Basic.lean::locate  reproduces  Basic.lean::cut: 219/305 = 72%
   TwoTapes.lean::tt_orbit_rsum  reproduces  TwoTapes.lean::tt_D_succ: 88/123 = 72%
   TwoTapes.lean::tt_D_level  reproduces  TwoTapes.lean::tt_D_succ: 88/123 = 72%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_unary_copy: 704/985 = 71%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 100/140 = 71%
   ZoneRebalance.lean::zr_time_asc  reproduces  ZoneRebalance.lean::zr_time_desc: 139/195 = 71%
   ZoneRebalance.lean::zr_body_post  reproduces  ZoneRebalance.lean::zr_return_post: 328/461 = 71%
   ZoneRebalance.lean::zr_grdOutBack  reproduces  ZoneRebalance.lean::zr_hmBack: 101/142 = 71%
   ZoneRebalance.lean::zr_outSeg_spec  reproduces  ZoneRebalance.lean::zr_prSeg_spec: 128/180 = 71%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::leftCfg_apply: 133/188 = 71%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 171/242 = 71%
   ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_rulerCopy_skip_pre: 214/303 = 71%
   ZoneRebalance.lean::zr_fpSeg  reproduces  ZoneRebalance.lean::zr_hmSeg: 192/272 = 71%
   ZoneRebalance.lean::zr_p2Body_hX  reproduces  ZoneRebalance.lean::zr_p1Body_hX: 84/119 = 71%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run: 151/214 = 71%
   ZoneRebalance.lean::zr_rowC_step  reproduces  ZoneRebalance.lean::zr_rowC_back: 103/146 = 71%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_body_post: 390/554 = 70%
   ZoneRebalance.lean::zr_rb_valid  reproduces  ZoneRebalance.lean::zr_dn_valid: 121/172 = 70%
   Simulation.lean::branchTM_computes  reproduces  Simulation.lean::rightCfg_apply: 135/192 = 70%
   ZoneRebalance.lean::zr_pinCopyContract  reproduces  ZoneRebalance.lean::zr_pinSkipContract: 90/128 = 70%
   Simulation.lean::rightCfg_run  reproduces  Simulation.lean::leftCfg_run: 71/101 = 70%
   AlphabetReduction.lean::alphabet_reduction_run  reproduces  Universal.lean::timedCut_live_before: 85/121 = 70%
   ZoneRebalance.lean::zr_time_desc  reproduces  ZoneRebalance.lean::zr_time_asc: 139/198 = 70%
   Basic.lean::traj_iff  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   Basic.lean::Frames.trans  reproduces  Basic.lean::endpoint_not_mem: 80/114 = 70%
   ZoneRebalance.lean::zr_rowP0  reproduces  ZoneRebalance.lean::zr_rowU: 87/124 = 70%
   Embed.lean::embedSilentTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 188/268 = 70%
   ZoneRebalance.lean::zr_p1Body_hX  reproduces  ZoneRebalance.lean::zr_p2Body_hX: 84/120 = 70%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_return_post: 322/461 = 70%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_initial_skip: 704/1008 = 70%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 132/189 = 70%
   TwoTapes.lean::tt_cs_round  reproduces  TwoTapes.lean::tt_T_ge: 87/125 = 70%
   ZoneRebalance.lean::zr_rowC_back  reproduces  ZoneRebalance.lean::zr_rowC_step: 103/148 = 70%
   ZoneRebalance.lean::zr_scanBody_bounds  reproduces  ZoneRebalance.lean::zr_wordTest_wordAt: 167/240 = 70%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_test_post: 407/585 = 70%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Simulation.lean::bufferedFirstCfg_init: 224/322 = 70%
   ZoneRebalance.lean::zr_wordTest_wordAt  reproduces  ZoneRebalance.lean::zr_pinTest_state: 105/151 = 70%
   ZoneRebalance.lean::zr_rowR_spec  reproduces  ZoneRebalance.lean::zr_rowLeft_spec: 332/479 = 69%
   ZoneRebalance.lean::zr_pinCopyContract  reproduces  ZoneRebalance.lean::zr_pinClearContract: 90/130 = 69%
   ZoneRebalance.lean::zr_p2_anchor  reproduces  ZoneRebalance.lean::zr_lb_anchor: 137/198 = 69%
   ZoneRebalance.lean::zr_p2Br_step  reproduces  ZoneRebalance.lean::zr_p1Br_step: 339/490 = 69%
   ZoneRebalance.lean::zr_scr_copy  reproduces  ZoneRebalance.lean::zr_copy0: 110/159 = 69%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_inSeg: 13224/19117 = 69%
   ZoneRebalance.lean::zr_hmGat  reproduces  ZoneRebalance.lean::zr_hmSc1: 4774/6905 = 69%
   Simulation.lean::leftCfg_run  reproduces  Simulation.lean::rightCfg_run: 71/103 = 69%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_hmGat: 6283/9115 = 69%
   ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_adjustedWalk_back_pre: 335/486 = 69%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 388/563 = 69%
   ZoneRebalance.lean::zr_shortPin_pre  reproduces  ZoneRebalance.lean::zr_scanPin_pre: 146/212 = 69%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightSeek_back_pre: 318/462 = 69%
   Deterministic.lean::ComputesInTimeAndSpace  reproduces  Deterministic.lean::haltsAtStep: 64/93 = 69%
   ZoneRebalance.lean::zr_pinRe_step  reproduces  ZoneRebalance.lean::zr_PinStep_exits: 200/291 = 69%
   ZoneRebalance.lean::zr_finalContract  reproduces  ZoneRebalance.lean::zr_shortContract: 340/495 = 69%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_body_post: 380/554 = 69%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 96/140 = 69%
   ZoneRebalance.lean::zr_rightRuler_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 96/140 = 69%
   ZoneRebalance.lean::zr_prSeg_spec  reproduces  ZoneRebalance.lean::zr_inSeg_spec: 148/216 = 69%
   Universal.lean::timedBorrow_value  reproduces  Universal.lean::timedBorrow_underflow: 91/133 = 68%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_hmSc2: 6157/8999 = 68%
   ZoneRebalance.lean::zr_p4Body  reproduces  ZoneRebalance.lean::zr_woBody: 191/280 = 68%
   ZoneRebalance.lean::zr_outSeg_spec  reproduces  ZoneRebalance.lean::zr_retSeg_spec: 103/151 = 68%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 384/563 = 68%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release: 774/1135 = 68%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_unary_copy: 671/985 = 68%
   SingleTape.lean::one_work_tape_binary_spaceUsed  reproduces  SingleTape.lean::one_work_tape_binary: 305/448 = 68%
   ZoneRebalance.lean::zr_rightLeft_link  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 140/206 = 68%
   ZoneRebalance.lean::zr_pinLoop  reproduces  ZoneRebalance.lean::zr_iterate_step: 95/140 = 68%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedCut_live_before: 82/121 = 68%
   ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_adjustedBack_copy_pre: 344/508 = 68%
   ZoneRebalance.lean::zr_p4Arm_step  reproduces  ZoneRebalance.lean::zr_p4_anchor: 240/355 = 68%
   ZoneRebalance.lean::zr_p3_round_box  reproduces  ZoneRebalance.lean::zr_p4_round_box: 881/1304 = 68%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_hmGat: 6142/9115 = 67%
   ZoneRebalance.lean::zr_finalContract  reproduces  ZoneRebalance.lean::zr_leftPassContract: 295/438 = 67%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_test_time: 68/101 = 67%
   ZoneRebalance.lean::zr_p3Body  reproduces  ZoneRebalance.lean::zr_p3U: 68/101 = 67%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_initial_skip: 678/1008 = 67%
   ZoneRebalance.lean::zr_rightLeftRow  reproduces  ZoneRebalance.lean::zr_rightReturnRow: 88/131 = 67%
   ZoneRebalance.lean::zr_rbBody  reproduces  ZoneRebalance.lean::zr_rbU: 65/97 = 67%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_initial_skip: 675/1008 = 67%
   ZoneRebalance.lean::zr_hmGat  reproduces  ZoneRebalance.lean::zr_hmSc2: 6023/8999 = 67%
   ZoneRebalance.lean::zr_pinRe_step  reproduces  ZoneRebalance.lean::zr_pinRe_ofSeg: 97/145 = 67%
   ZoneRebalance.lean::zr_PinStep_exits  reproduces  ZoneRebalance.lean::zr_pinRe_ofSeg: 97/145 = 67%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_pinTest_state: 101/151 = 67%
   ZoneRebalance.lean::zr_scanBody_bounds  reproduces  ZoneRebalance.lean::zr_pinTest_state: 101/151 = 67%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 204/305 = 67%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_body_post: 370/554 = 67%
   ZoneRebalance.lean::zr_loop_zone_test  reproduces  ZoneRebalance.lean::zr_loop_zone_word: 187/280 = 67%
   ZoneRebalance.lean::zr_PinStep_exits  reproduces  ZoneRebalance.lean::zr_pinRe_step: 200/300 = 67%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_pair_separator: 138/207 = 67%
   ZoneRebalance.lean::zr_scan_round  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 112/168 = 67%
   Universal.lean::timed_replay  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 112/168 = 67%
   Universal.lean::timedBorrow_fold  reproduces  Universal.lean::timedBorrow_length: 64/96 = 67%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_heads: 395/594 = 66%
   Embed.lean::embedSilent_apply  reproduces  Embed.lean::embedEmit_apply: 168/253 = 66%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_test_time: 67/101 = 66%
   ZoneRebalance.lean::zr_return_time  reproduces  ZoneRebalance.lean::zr_test_time: 67/101 = 66%
   ZoneRebalance.lean::zr_rightLeftContract  reproduces  ZoneRebalance.lean::zr_extendContract: 120/181 = 66%
   ZoneRebalance.lean::zr_extendContract  reproduces  ZoneRebalance.lean::zr_rightLeftContract: 120/181 = 66%
   Universal.lean::timed_replay  reproduces  Universal.lean::timedCapture_run: 112/169 = 66%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_body_bounds: 327/494 = 66%
   ZoneRebalance.lean::zr_lbPass  reproduces  ZoneRebalance.lean::zr_rbPass: 455/688 = 66%
   AlphabetReduction.lean::arEmission_in_image  reproduces  Universal.lean::timedCut_live_before: 80/121 = 66%
   ZoneRebalance.lean::zr_hmSc2  reproduces  ZoneRebalance.lean::zr_hmGat: 6023/9115 = 66%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_shortContract: 327/495 = 66%
   ZoneRebalance.lean::zr_p1Pass  reproduces  ZoneRebalance.lean::zr_p2Pass: 504/763 = 66%
   ZoneRebalance.lean::zr_hmSc2  reproduces  ZoneRebalance.lean::zr_hmSc1: 4557/6905 = 66%
   ZoneRebalance.lean::zr_p4Body  reproduces  ZoneRebalance.lean::zr_p4U: 64/97 = 66%
   ZoneRebalance.lean::zr_adjustedWalk_back_pre  reproduces  ZoneRebalance.lean::zr_adjustedBack_copy_pre: 335/508 = 66%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_fields: 1003/1521 = 66%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_pos_of_ne_right: 71/108 = 66%
   ZoneRebalance.lean::zr_p1Lead  reproduces  ZoneRebalance.lean::zr_p2Lead: 957/1457 = 66%
   ZoneRebalance.lean::zr_mir_step  reproduces  ZoneRebalance.lean::zr_mir_mir: 155/236 = 66%
   ZoneRebalance.lean::zr_pinBackContract  reproduces  ZoneRebalance.lean::zr_pinSkipContract: 84/128 = 66%
   AlphabetReduction.lean::arWriteCfg_finish  reproduces  AlphabetReduction.lean::arMoveCfg_finish: 166/253 = 66%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_adjustedBack_copy_pre: 333/508 = 66%
   Universal.lean::timedFrame_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 110/168 = 65%
   ZoneRebalance.lean::zr_decEqLoopPh  reproduces  ZoneRebalance.lean::zr_fintypeLoopPh: 72/110 = 65%
   ZoneRebalance.lean::zr_inTest_step  reproduces  ZoneRebalance.lean::zr_grdIn_step: 253/387 = 65%
   ZoneRebalance.lean::zr_rightReturn_time  reproduces  ZoneRebalance.lean::zr_test_time: 66/101 = 65%
   ZoneRebalance.lean::zr_rightPass_time  reproduces  ZoneRebalance.lean::zr_test_time: 66/101 = 65%
   ZoneRebalance.lean::zr_host_dispatch_run  reproduces  ZoneRebalance.lean::zoneRowPre_mapState_iff: 64/98 = 65%
   Universal.lean::timedPrefix_live  reproduces  Universal.lean::timedCut_live_before: 79/121 = 65%
   Universal.lean::timed_pair_get  reproduces  Universal.lean::timed_pair_separator: 135/207 = 65%
   SingleTape.lean::sweep_grow_left_block  reproduces  SingleTape.lean::sweep_grow_right_block: 343/526 = 65%
   SingleTape.lean::sweep_init_block  reproduces  SingleTape.lean::sweep_grow_left_block: 446/684 = 65%
   ZoneRebalance.lean::zr_scr_copy  reproduces  ZoneRebalance.lean::zr_heads_ext: 99/152 = 65%
   Universal.lean::timedFrame_run  reproduces  Universal.lean::timedCapture_run: 110/169 = 65%
   ZoneRebalance.lean::zr_fp8  reproduces  ZoneRebalance.lean::zr_fp3: 225/346 = 65%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedPrefix_complete: 507/780 = 65%
   ZoneRebalance.lean::zr_retSeg_spec  reproduces  ZoneRebalance.lean::zr_prSeg_spec: 117/180 = 65%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_test_post: 380/585 = 65%
   ZoneRebalance.lean::zr_shortPin_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 109/168 = 65%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 109/168 = 65%
   ZoneRebalance.lean::zr_rightReturn_link  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 109/168 = 65%
   ZoneRebalance.lean::zr_leftWalk_fields  reproduces  ZoneRebalance.lean::zr_return_time: 96/148 = 65%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_return_time: 96/148 = 65%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_body_post: 358/554 = 65%
   Simulation.lean::rightCfg  reproduces  Simulation.lean::leftCfg: 84/130 = 65%
   Simulation.lean::leftCfg  reproduces  Simulation.lean::rightCfg: 84/130 = 65%
   ZoneRebalance.lean::zr_grdOut  reproduces  ZoneRebalance.lean::zr_grdIn: 155/240 = 65%
   ZoneRebalance.lean::zr_rightPass_bounds  reproduces  ZoneRebalance.lean::zr_body_bounds: 319/494 = 65%
   ZoneRebalance.lean::zr_leftWrite_pre  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 133/206 = 65%
   ZoneRebalance.lean::zr_p1Peek_step  reproduces  ZoneRebalance.lean::zr_p2Peek_step: 224/347 = 65%
   ZoneRebalance.lean::zr_blankBranchContract  reproduces  ZoneRebalance.lean::zr_slotBranchContract: 224/348 = 64%
   Simulation.lean::bufferedScanCfg_run  reproduces  Simulation.lean::bufferedFirstCfg_rewind: 473/735 = 64%
   SingleTape.lean::dgInput_read  reproduces  SingleTape.lean::sweepInput_read: 189/294 = 64%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 108/168 = 64%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 108/168 = 64%
   SingleTape.lean::dg_unused_space  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed: 81/126 = 64%
   ZoneRebalance.lean::zr_woPass  reproduces  ZoneRebalance.lean::zr_p4Pass: 451/702 = 64%
   ZoneRebalance.lean::zr_woPass  reproduces  ZoneRebalance.lean::zr_p3Pass: 451/702 = 64%
   ZoneRebalance.lean::zr_twoSteps_fields  reproduces  ZoneRebalance.lean::zr_return_post: 296/461 = 64%
   ZoneRebalance.lean::zr_lbBack  reproduces  ZoneRebalance.lean::zr_woBack: 95/148 = 64%
   ZoneRebalance.lean::zr_loop_orbit  reproduces  ZoneRebalance.lean::zr_loopAt_fields: 75/117 = 64%
   Zone.lean::zoneSide_shiftInW  reproduces  Zone.lean::zoneSide_shiftOutW: 296/462 = 64%
   Universal.lean::timedCapture_run  reproduces  Simulation.lean::bufferedFirstCfg_run: 146/228 = 64%
   ZoneRebalance.lean::zr_p1Br_step  reproduces  ZoneRebalance.lean::zr_p1_anchor_box: 176/275 = 64%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_body_post: 354/554 = 64%
   ZoneRebalance.lean::zr_shiftIn_tape  reproduces  ZoneRebalance.lean::zr_shiftIn_off: 106/166 = 64%
   ZoneRebalance.lean::zr_inSeg_spec  reproduces  ZoneRebalance.lean::zr_outSeg_spec: 166/260 = 64%
   Embed.lean::embedEmitTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 171/268 = 64%
   ZoneRebalance.lean::zr_woBack  reproduces  ZoneRebalance.lean::zr_lbBack: 95/149 = 64%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_run  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_firstReturn: 151/237 = 64%
   ZoneRebalance.lean::zr_rightRuler_write_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 107/168 = 64%
   ZoneRebalance.lean::zr_rightLeftFinal_link  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 107/168 = 64%
   ZoneRebalance.lean::zr_branchBack_hX  reproduces  ZoneRebalance.lean::zr_seqBack_hX: 238/374 = 64%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Admin_apply: 168/264 = 64%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 358/563 = 64%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timedClockPrefix_length: 89/140 = 64%
   ZoneRebalance.lean::zr_writeHalves_post  reproduces  ZoneRebalance.lean::zr_return_post: 293/461 = 64%
   ZoneRebalance.lean::zr_rightPass_time  reproduces  ZoneRebalance.lean::zr_return_time: 94/148 = 64%
   AlphabetReduction.lean::alphabet_reduction_spaceUsed  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed: 80/126 = 63%
   Universal.lean::timed_output_step  reproduces  Universal.lean::timedClock_step: 158/249 = 63%
   Universal.lean::timedCaptureCfg  reproduces  Simulation.lean::bufferedFirstCfg: 109/172 = 63%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_test_time: 64/101 = 63%
   ZoneRebalance.lean::zr_p1_facts  reproduces  ZoneRebalance.lean::zr_p2_facts: 102/161 = 63%
   ZoneRebalance.lean::zr_zonedTape_update  reproduces  ZoneRebalance.lean::zr_zonedTape_inr: 281/444 = 63%
   SingleTape.lean::dg_turn_with_growth  reproduces  SingleTape.lean::dg_turn_without_growth: 462/730 = 63%
   ZoneRebalance.lean::zr_scan_round  reproduces  ZoneRebalance.lean::zoneRowPre_mapState_iff: 62/98 = 63%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_countClearContract: 601/950 = 63%
   ZoneRebalance.lean::zr_woLead_step  reproduces  ZoneRebalance.lean::zr_lbArm_step: 353/558 = 63%
   ZoneRebalance.lean::zr_rightReturn_post  reproduces  ZoneRebalance.lean::zr_rightReturn_pre: 115/182 = 63%
   ZoneRebalance.lean::zr_shiftOut_tape  reproduces  ZoneRebalance.lean::zr_shiftOut_off: 127/201 = 63%
   ZoneRebalance.lean::zr_writeHalves_post  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 106/168 = 63%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_hmSc1: 4355/6905 = 63%
   ZoneRebalance.lean::zr_leftMoveContract  reproduces  ZoneRebalance.lean::zr_shortContract: 312/495 = 63%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_leftMove_fields: 937/1487 = 63%
   ZoneRebalance.lean::zr_rightReturn_pre  reproduces  ZoneRebalance.lean::zr_extend_pre: 114/181 = 63%
   ZoneRebalance.lean::zr_fpG5  reproduces  ZoneRebalance.lean::zr_fpG4: 374/594 = 63%
   ZoneRebalance.lean::zr_scanPhaseContract  reproduces  ZoneRebalance.lean::zr_scanBack: 85/135 = 63%
   Universal.lean::timedCapture_step  reproduces  Simulation.lean::bufferedFirstCfg_step: 725/1152 = 63%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 354/563 = 63%
   SingleTape.lean::dg_unused_space  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 71/113 = 63%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_scanPin_pre: 133/212 = 63%
   ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_rightSeekBack_post: 579/923 = 63%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timed_pair_get: 173/276 = 63%
   ZoneRebalance.lean::zr_rightLeft_pre  reproduces  ZoneRebalance.lean::zr_rightReturn_pre: 114/182 = 63%
   ZoneRebalance.lean::zr_extend_pre  reproduces  ZoneRebalance.lean::zr_rightReturn_pre: 114/182 = 63%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_body_post: 347/554 = 63%
   ZoneRebalance.lean::zr_shortPin_pre  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 129/206 = 63%
   ZoneRebalance.lean::zr_retSeg_spec  reproduces  ZoneRebalance.lean::zr_hmSeg_spec: 77/123 = 63%
   TwoTapes.lean::tt_cs_round  reproduces  TwoTapes.lean::tt_D_succ: 77/123 = 63%
   Universal.lean::timed_clock_separator  reproduces  Universal.lean::timed_clock_get: 236/377 = 63%
   ZoneRebalance.lean::zr_return_bounds  reproduces  ZoneRebalance.lean::zr_body_bounds: 309/494 = 63%
   ZoneRebalance.lean::zr_goRoom_step  reproduces  ZoneRebalance.lean::zr_goRoom_back: 156/250 = 62%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_rightLeftFinal_link: 287/460 = 62%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_leftPassContract: 273/438 = 62%
   ZoneRebalance.lean::zr_scr_clear  reproduces  ZoneRebalance.lean::zr_scr_copy: 441/708 = 62%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_retSeg: 1810/2906 = 62%
   ZoneRebalance.lean::zr_seekStart_pre  reproduces  ZoneRebalance.lean::zr_left_reach: 94/151 = 62%
   ZoneRebalance.lean::zr_rbArm_step  reproduces  ZoneRebalance.lean::zr_lbArm_step: 347/558 = 62%
   Zone.lean::zoneShiftIndex_nonempty  reproduces  Zone.lean::zoneShiftIndex_empty: 115/185 = 62%
   Basic.lean::RoundContract  reproduces  Basic.lean::Contract: 302/487 = 62%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_frame: 70/113 = 62%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_return_post: 285/461 = 62%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Simulation.lean::bufferedFirstCfg_init: 199/322 = 62%
   ZoneRebalance.lean::zr_pinSkipContract  reproduces  ZoneRebalance.lean::zr_pinBackContract: 84/136 = 62%
   ZoneRebalance.lean::zr_inPass_out  reproduces  ZoneRebalance.lean::zr_pair_pass: 92/149 = 62%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_scanBody_bounds: 408/661 = 62%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 127/206 = 62%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 127/206 = 62%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead_frame: 188/305 = 62%
   ZoneRebalance.lean::zr_rightReturn_bounds  reproduces  ZoneRebalance.lean::zr_rightReturn_pre: 112/182 = 62%
   ZoneRebalance.lean::zr_p4Tau_le  reproduces  ZoneRebalance.lean::zr_p3Tau_le: 88/143 = 62%
   ZoneRebalance.lean::zr_pinBackContract  reproduces  ZoneRebalance.lean::zr_pinClearContract: 80/130 = 62%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_hmSc1: 4242/6905 = 61%
   ZoneRebalance.lean::zr_leftWalk_fields  reproduces  ZoneRebalance.lean::zr_test_time: 62/101 = 61%
   Universal.lean::timed_replay  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timedFrame_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Universal.lean::timedCapture_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   Simulation.lean::bufferedFirstCfg_run  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom: 92/150 = 61%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 103/168 = 61%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_leftMove_link₁: 190/310 = 61%
   ZoneRebalance.lean::zr_rightReturn_pre  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 114/186 = 61%
   ZoneRebalance.lean::zr_scratchBackContract  reproduces  ZoneRebalance.lean::zr_scratchSkipContract: 71/116 = 61%
   ZoneRebalance.lean::zr_fpG0  reproduces  ZoneRebalance.lean::zr_fpG10: 350/572 = 61%
   ZoneRebalance.lean::zr_rightLeftFinal_link  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 126/206 = 61%
   Embed.lean::embedEmitCfg  reproduces  Embed.lean::embedSilentCfg: 165/270 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 132/216 = 61%
   ZoneRebalance.lean::zr_fpG10  reproduces  ZoneRebalance.lean::zr_fpG0: 350/573 = 61%
   SingleTape.lean::dg_left_span  reproduces  SingleTape.lean::dg_right_span: 312/511 = 61%
   ZoneRebalance.lean::zr_goRoom  reproduces  ZoneRebalance.lean::zr_goOn: 105/172 = 61%
   ZoneRebalance.lean::zr_fintypeLoopPh  reproduces  ZoneRebalance.lean::zr_decEqLoopPh: 72/118 = 61%
   SingleTape.lean::tapeZone_length  reproduces  SingleTape.lean::read_zone: 78/128 = 61%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_pinTest_state: 92/151 = 61%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_return_time: 90/148 = 61%
   ZoneRebalance.lean::zr_rightPass_pre  reproduces  ZoneRebalance.lean::zr_extend_pre: 110/181 = 61%
   ZoneRebalance.lean::zr_rightPass_post  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 85/140 = 61%
   Basic.lean::traj_iff  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Basic.lean::Frames.trans  reproduces  Basic.lean::Cfg.SameOutside.keep_blank: 80/132 = 61%
   Simulation.lean::bufferedSecondCfg  reproduces  Simulation.lean::bufferedScanCfg: 83/137 = 61%
   ZoneRebalance.lean::zr_short_fields  reproduces  CfgFacts.lean::Cfg.mapState_eq_of_fields: 106/175 = 61%
   ZoneRebalance.lean::zr_scr_clear  reproduces  ZoneRebalance.lean::zr_heads_ext: 92/152 = 61%
   ZoneRebalance.lean::zr_outSeg  reproduces  ZoneRebalance.lean::zr_retSeg: 1758/2906 = 60%
   ZoneRebalance.lean::zr_rightPass_pre  reproduces  ZoneRebalance.lean::zr_rightReturn_pre: 110/182 = 60%
   Simulation.lean::bufferedScanCfg_run  reproduces  Universal.lean::timedCapture_init: 192/318 = 60%
   Simulation.lean::bufferedFirstCfg_rewind  reproduces  Universal.lean::timedCapture_init: 192/318 = 60%
   ZoneRebalance.lean::zr_rightPass_post  reproduces  ZoneRebalance.lean::zr_test_post: 353/585 = 60%
   ZoneRebalance.lean::zr_shortContract  reproduces  ZoneRebalance.lean::zr_leftPassContract: 264/438 = 60%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_rightLeftFinal_link: 277/460 = 60%
   ZoneRebalance.lean::zr_pinWalkContract  reproduces  ZoneRebalance.lean::zr_pinSkipContract: 77/128 = 60%
   ZoneRebalance.lean::zr_mir_box  reproduces  ZoneRebalance.lean::zr_mir_lockstep: 107/178 = 60%
   ZoneRebalance.lean::zr_scanBodyRow  reproduces  ZoneRebalance.lean::zr_scanBack: 81/135 = 60%
   ZoneRebalance.lean::zr_rulerCopyContract  reproduces  ZoneRebalance.lean::zr_halfCopyContract: 66/110 = 60%
   ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_body_post: 332/554 = 60%
   ZoneRebalance.lean::zr_shiftOut_off  reproduces  ZoneRebalance.lean::zr_shiftOut_zero: 109/182 = 60%
   ZoneRebalance.lean::exists_zoneExtendTM  reproduces  ZoneRebalance.lean::zr_heads_ext: 91/152 = 60%
   ZoneRebalance.lean::zr_rightPass_bounds  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 113/189 = 60%
   ZoneRebalance.lean::zr_rowU  reproduces  ZoneRebalance.lean::zr_rowP0: 87/146 = 60%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_twoSteps_fields: 619/1039 = 60%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedCut_skip_fixed: 420/705 = 60%
   Universal.lean::timedClock_step  reproduces  Universal.lean::timed_output_step: 158/266 = 59%
   ZoneRebalance.lean::zr_outSeg_spec  reproduces  ZoneRebalance.lean::zr_hmSeg_spec: 73/123 = 59%
   ZoneRebalance.lean::zr_inSeg_spec  reproduces  ZoneRebalance.lean::zr_hmSeg_spec: 73/123 = 59%
   ZoneRebalance.lean::zr_rightLeft_link  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 83/140 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 80/135 = 59%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 80/135 = 59%
   Simulation.lean::bufferedFirstCfg  reproduces  Universal.lean::timedCaptureCfg: 109/184 = 59%
   ZoneRebalance.lean::zr_pinWalkContract  reproduces  ZoneRebalance.lean::zr_pinClearContract: 77/130 = 59%
   ZoneRebalance.lean::zr_return_post  reproduces  ZoneRebalance.lean::zr_body_post: 328/554 = 59%
   ZoneRebalance.lean::zr_rightPass_pre  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 110/186 = 59%
   ZoneRebalance.lean::zr_fpG6  reproduces  ZoneRebalance.lean::zr_fpG8: 619/1047 = 59%
   ZoneRebalance.lean::zr_lb_anchor  reproduces  ZoneRebalance.lean::zr_p2_anchor: 137/232 = 59%
   ZoneRebalance.lean::zr_p4Pass  reproduces  ZoneRebalance.lean::zr_woPass: 451/765 = 59%
   ZoneRebalance.lean::zr_p3Pass  reproduces  ZoneRebalance.lean::zr_woPass: 451/765 = 59%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_pinTest_state: 89/151 = 59%
   ZoneRebalance.lean::zr_zonedTape_update  reproduces  ZoneRebalance.lean::zr_slot_track: 241/409 = 59%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_countClear_fields: 1131/1920 = 59%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightSeek_back_pre: 272/462 = 59%
   ZoneRebalance.lean::zr_out2Test_step  reproduces  ZoneRebalance.lean::zr_hmTest_step: 246/418 = 59%
   ZoneRebalance.lean::zr_out1Test_step  reproduces  ZoneRebalance.lean::zr_hmTest_step: 246/418 = 59%
   ZoneRebalance.lean::zr_pinCopyContract  reproduces  ZoneRebalance.lean::zr_pinBackContract: 80/136 = 59%
   ZoneRebalance.lean::zr_pinClearContract  reproduces  ZoneRebalance.lean::zr_pinBackContract: 80/136 = 59%
   ZoneRebalance.lean::zr_adjustedWalk_post  reproduces  ZoneRebalance.lean::zr_test_post: 344/585 = 59%
   Universal.lean::timed_apply_record  reproduces  Universal.lean::timedCut_Interpreter_first: 169/288 = 59%
   ZoneRebalance.lean::zr_hmSkip_step  reproduces  ZoneRebalance.lean::zr_hmLead_step: 213/363 = 59%
   Configuration.lean::moveInputPos_rightBoundary  reproduces  Configuration.lean::moveInputPos_neg_of_ne_left: 68/116 = 59%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_scan_fields: 879/1500 = 59%
   ZoneRebalance.lean::zr_scanCfg_marked  reproduces  ZoneRebalance.lean::zr_scanCfg_fields: 92/157 = 59%
   ZoneRebalance.lean::zr_hmSkip  reproduces  ZoneRebalance.lean::zr_hmLead: 128/219 = 58%
   ZoneRebalance.lean::zr_pinSkipContract  reproduces  ZoneRebalance.lean::zr_pinCopyContract: 90/154 = 58%
   ZoneRebalance.lean::zr_pinClearContract  reproduces  ZoneRebalance.lean::zr_pinCopyContract: 90/154 = 58%
   Simulation.lean::bufferedFirstCfg_step  reproduces  Universal.lean::timedCapture_step: 725/1241 = 58%
   ZoneRebalance.lean::zr_p4_anchor  reproduces  ZoneRebalance.lean::zr_wo_anchor: 143/245 = 58%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_wordTest_wordAt: 140/240 = 58%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM: 148/254 = 58%
   ZoneTape.lean::zonedTape_right  reproduces  ZoneTape.lean::zonedTape_right_sep: 92/158 = 58%
   TwoTapes.lean::tt_T  reproduces  TwoTapes.lean::tt_D: 85/146 = 58%
   ZoneRebalance.lean::zr_p2Br_step  reproduces  ZoneRebalance.lean::zr_p2_anchor: 135/232 = 58%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_rightSeekBack_ruler_pre: 298/513 = 58%
   ZoneRebalance.lean::zr_wo_anchor  reproduces  ZoneRebalance.lean::zr_lb_anchor: 115/198 = 58%
   SingleTape.lean::sweepRevCfg_write  reproduces  SingleTape.lean::sweep_turn_right: 189/326 = 58%
   Embed.lean::embedThroughHalt  reproduces  Universal.lean::timedFrame_run: 73/126 = 58%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::ReturnContract.release  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::RoundContract.release: 774/1336 = 58%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 81/140 = 58%
   ZoneRebalance.lean::zr_grdIn  reproduces  ZoneRebalance.lean::zr_grdOut: 155/268 = 58%
   ZoneRebalance.lean::zr_finalContract  reproduces  ZoneRebalance.lean::zr_countClearContract: 549/950 = 58%
   ZoneRebalance.lean::zr_p2Peek_step  reproduces  ZoneRebalance.lean::zr_p1Peek_step: 224/388 = 58%
   ZoneRebalance.lean::zr_hmZ_eq  reproduces  ZoneRebalance.lean::zr_slot_track: 236/409 = 58%
   ZoneRebalance.lean::zr_scanBody_bounds  reproduces  ZoneRebalance.lean::zr_body_bounds: 285/494 = 58%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_leftMove_fields: 857/1487 = 58%
   Embed.lean::embedSilentRetTM_run  reproduces  Embed.lean::embedSilentTM_runFrom: 68/118 = 58%
   TwoTapes.lean::tt_cost  reproduces  TwoTapes.lean::tt_T_ge: 72/125 = 58%
   TwoTapes.lean::tt_idxR  reproduces  TwoTapes.lean::tt_D: 84/146 = 58%
   ZoneRebalance.lean::zr_rightLeft_fields  reproduces  ZoneRebalance.lean::zr_extend_pre: 104/181 = 57%
   ZoneRebalance.lean::zr_extend_fields  reproduces  ZoneRebalance.lean::zr_extend_pre: 104/181 = 57%
   ZoneRebalance.lean::zr_p4Arm_step  reproduces  ZoneRebalance.lean::zr_p3Arm_step: 791/1377 = 57%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_rightLeftFinal_link: 264/460 = 57%
   SingleTape.lean::dg_end_with_growth  reproduces  SingleTape.lean::dg_turn_with_growth: 736/1283 = 57%
   ZoneRebalance.lean::zr_shiftIn_tape  reproduces  ZoneRebalance.lean::zr_shiftOut_tape: 916/1597 = 57%
   ZoneRebalance.lean::zr_loop_home_test  reproduces  ZoneRebalance.lean::zr_loop_home_word: 137/239 = 57%
   ZoneRebalance.lean::zr_finalContract  reproduces  ZoneRebalance.lean::zr_scanContract: 292/510 = 57%
   Universal.lean::timed_universal  reproduces  Universal.lean::timed_universal_concrete: 384/671 = 57%
   Basic.lean::time_envelope  reproduces  Basic.lean::time_box: 123/215 = 57%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_rightSeekBack_post: 528/923 = 57%
   SingleTape.lean::sweep_prepare  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   Simulation.lean::bufferedSecondCfg_run  reproduces  Universal.lean::timedFrame_run: 72/126 = 57%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_test_post: 334/585 = 57%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_wordTest_wordAt: 137/240 = 57%
   ZoneRebalance.lean::zr_rightPass_post  reproduces  ZoneRebalance.lean::zr_return_post: 263/461 = 57%
   Embed.lean::embedEmitTM_visitedByTapeHead_frame  reproduces  Embed.lean::embedEmitTM_visitedByTapeHead: 138/242 = 57%
   AlphabetReduction.lean::arCfg_run  reproduces  Basic.lean::runFrom: 94/165 = 57%
   ZoneRebalance.lean::zr_inTest_step  reproduces  ZoneRebalance.lean::zr_hmTest_step: 238/418 = 57%
   ZoneRebalance.lean::zr_fpG4  reproduces  ZoneRebalance.lean::zr_fpG5: 374/657 = 57%
   ZoneRebalance.lean::zr_countClearContract  reproduces  ZoneRebalance.lean::zr_returnContract: 214/376 = 57%
   ZoneRebalance.lean::zr_rightLeft_post  reproduces  ZoneRebalance.lean::zr_extend_pre: 103/181 = 57%
   ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_innerCopy_adjusted_pre: 344/605 = 57%
   TwoTapes.lean::tt_cs_round  reproduces  TwoTapes.lean::tt_orbit_rsum: 141/248 = 57%
   ZoneRebalance.lean::zr_inOff_esc  reproduces  ZoneRebalance.lean::zr_inOff_valid: 129/227 = 57%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_left_sep: 92/162 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_unary_copy: 558/985 = 57%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_twoSteps_fields: 588/1039 = 57%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedCut_skip_unary: 709/1254 = 57%
   Embed.lean::embedSilentRetTM_visitedByTapeHead  reproduces  Embed.lean::embedEmitRetTM_visitedByTapeHead: 65/115 = 57%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_leftMove_fields: 840/1487 = 56%
   ZoneRebalance.lean::zr_retSeg_spec  reproduces  ZoneRebalance.lean::zr_inSeg_spec: 122/216 = 56%
   ZoneRebalance.lean::zr_test_post  reproduces  ZoneRebalance.lean::zr_return_post: 260/461 = 56%
   Universal.lean::timedPrefix_clock_end  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedPrefix_clock  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   Universal.lean::timedCut_state_rewind  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   SingleTape.lean::sweep_finish  reproduces  Universal.lean::timedFrame_run: 71/126 = 56%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_rightSeekBack_post: 520/923 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_step_inr: 76/135 = 56%
   Finite.lean::step_output_prepend  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_right: 76/135 = 56%
   ZoneRebalance.lean::zr_rowLeft_spec  reproduces  ZoneRebalance.lean::zr_rowR_spec: 332/590 = 56%
   ZoneRebalance.lean::zr_hmGat  reproduces  ZoneRebalance.lean::zr_prSeg: 2585/4602 = 56%
   ZoneRebalance.lean::zr_hmLead  reproduces  ZoneRebalance.lean::zr_hmSkip: 128/228 = 56%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_scanPin_pre: 119/212 = 56%
   ZoneRebalance.lean::zr_fpG3  reproduces  ZoneRebalance.lean::zr_fpG9: 385/686 = 56%
   ZoneRebalance.lean::zr_finalContract  reproduces  ZoneRebalance.lean::zr_returnContract: 211/376 = 56%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_adjustedBack_post: 581/1036 = 56%
   SingleTape.lean::dg_collect  reproduces  SingleTape.lean::dg_read: 120/214 = 56%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_leftMoveContract: 640/1142 = 56%
   StateRenaming.lean::MultiTapeTM.runFrom_mapState_of_agreeOn  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamComp_step_left: 121/216 = 56%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_scan_fields: 840/1500 = 56%
   ZoneRebalance.lean::zr_p1Tau_le  reproduces  ZoneRebalance.lean::zr_p2Tau_le: 70/125 = 56%
   ZoneRebalance.lean::zr_rightLeft_fields  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 104/186 = 56%
   ZoneRebalance.lean::zr_extend_fields  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 104/186 = 56%
   ZoneRebalance.lean::zr_fpG2  reproduces  ZoneRebalance.lean::zr_fpG3: 391/701 = 56%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 314/563 = 56%
   SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 63/113 = 56%
   Embed.lean::embedSilentTM_visitedByTapeHead  reproduces  Embed.lean::embedSilentTM_frame: 63/113 = 56%
   AlphabetReduction.lean::alphabet_reduction_spaceUsed  reproduces  StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed: 63/113 = 56%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_leftPass_fields: 1191/2137 = 56%
   ZoneRebalance.lean::zr_rightReturn_link  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 78/140 = 56%
   ZoneRebalance.lean::zr_leftWrite_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 78/140 = 56%
   ZoneRebalance.lean::zr_leftMove_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 78/140 = 56%
   Universal.lean::timed_clock_get  reproduces  Universal.lean::timedClockPrefix_length: 78/140 = 56%
   Basic.lean::runFrom  reproduces  AlphabetReduction.lean::arCfg_run: 94/169 = 56%
   SingleTape.lean::dg_init  reproduces  SingleTape.lean::dg_right_span: 284/511 = 56%
   Universal.lean::timedPrefix_complete  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedPrefix_code  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamReleaseTM_runFrom_pos  reproduces  Universal.lean::timedFrame_run: 70/126 = 56%
   ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_test_post: 324/585 = 55%
   ZoneRebalance.lean::zr_PinStep_exits  reproduces  ZoneRebalance.lean::zr_singleton_fields: 103/186 = 55%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_unary: 694/1254 = 55%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_scanBodyContract: 255/461 = 55%
   ZoneRebalance.lean::zr_twoSteps_fields  reproduces  ZoneRebalance.lean::zr_test_post: 323/585 = 55%
   TwoTapes.lean::tt_Dtr_level_mono  reproduces  TwoTapes.lean::tt_Dtr_other: 321/582 = 55%
   ZoneRebalance.lean::zr_countClearContract  reproduces  ZoneRebalance.lean::zr_shortContract: 273/495 = 55%
   ZoneRebalance.lean::zr_pinWalkContract  reproduces  ZoneRebalance.lean::zr_pinBackContract: 75/136 = 55%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_test_post: 322/585 = 55%
   Simulation.lean::bufferedSecondCfg_step  reproduces  Universal.lean::timedCapture_init: 175/318 = 55%
   ZoneRebalance.lean::zr_hmSeg_spec  reproduces  ZoneRebalance.lean::zr_prSeg_spec: 99/180 = 55%
   ZoneRebalance.lean::zr_rightRuler_write_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 77/140 = 55%
   Simulation.lean::rewind_from_any  reproduces  Simulation.lean::timed_rewind: 239/435 = 55%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_adjustedWalk_back_pre: 267/486 = 55%
   ZoneRebalance.lean::zr_fpG9  reproduces  ZoneRebalance.lean::zr_fpG3: 385/701 = 55%
   ZoneRebalance.lean::zr_fold_desc  reproduces  ZoneRebalance.lean::zr_pxFold_id: 67/122 = 55%
   ZoneRebalance.lean::zr_rightPass_bounds  reproduces  ZoneRebalance.lean::zr_return_bounds: 309/563 = 55%
   ZoneRebalance.lean::zr_body_bounds  reproduces  ZoneRebalance.lean::zr_return_bounds: 309/563 = 55%
   ZoneRebalance.lean::zr_pinCell_step  reproduces  ZoneRebalance.lean::zr_singleton_fields: 102/186 = 55%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 102/186 = 55%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 102/186 = 55%
   ZoneRebalance.lean::zr_leftMoveContract  reproduces  ZoneRebalance.lean::zr_leftPassContract: 240/438 = 55%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left: 92/168 = 55%
   Universal.lean::timedCut_skip_groups  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Universal.lean::timedCut_prepare_next  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   SingleTape.lean::dg_simulate  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   Simulation.lean::bufferedScanCfg_run  reproduces  Universal.lean::timedFrame_run: 69/126 = 55%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_return_time: 81/148 = 55%
   SingleTape.lean::write_zone  reproduces  SingleTape.lean::read_zone: 70/128 = 55%
   SingleTape.lean::dg_right_span  reproduces  SingleTape.lean::dg_left_span: 312/571 = 55%
   ZoneRebalance.lean::zr_shiftIn_tape  reproduces  ZoneRebalance.lean::zr_shiftIn_zero: 89/163 = 55%
   ZoneTape.lean::zonedTape_left_word  reproduces  ZoneTape.lean::zonedTape_right_word: 285/522 = 55%
   StepBlockForward.lean::fl_restore  reproduces  StepBlockForward.lean::fl_home: 78/143 = 55%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_scan_fields: 817/1500 = 54%
   SymbolLift.lean::MultiTapeTM.liftSymbols_runFrom  reproduces  Universal.lean::timedCapture_run: 92/169 = 54%
   ZoneRebalance.lean::zr_lbArm_step  reproduces  ZoneRebalance.lean::zr_woLead_step: 353/649 = 54%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_test_post: 318/585 = 54%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedCut_skip_fixed: 383/705 = 54%
   ZoneRebalance.lean::zr_halfWriteContract  reproduces  ZoneRebalance.lean::zr_scratchSkipContract: 63/116 = 54%
   ZoneRebalance.lean::zr_shortPin_pre  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 76/140 = 54%
   ZoneRebalance.lean::zr_scan_round  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 76/140 = 54%
   ZoneRebalance.lean::zr_rightLeftFinal_link  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 76/140 = 54%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 76/140 = 54%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_scan_fields: 814/1500 = 54%
   ZoneRebalance.lean::zr_shiftOut_zero  reproduces  ZoneRebalance.lean::zr_shiftOut_off: 109/201 = 54%
   SingleTape.lean::read_zone  reproduces  SingleTape.lean::tapeZone_length: 78/144 = 54%
   ZoneRebalance.lean::zr_p4_round_box  reproduces  ZoneRebalance.lean::zr_p3_round_box: 881/1628 = 54%
   ZoneRebalance.lean::zr_loop_zone_word  reproduces  ZoneRebalance.lean::zr_loop_zone_test: 187/346 = 54%
   ZoneRebalance.lean::zr_leftMoveContract  reproduces  ZoneRebalance.lean::zr_countClearContract: 513/950 = 54%
   StepBlockForward.lean::fl_round  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   SingleTape.lean::sweep_init  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   AlphabetReduction.lean::arSpacePhase_run  reproduces  Universal.lean::timedFrame_run: 68/126 = 54%
   Zone.lean::zoneCascadeRight_lengths  reproduces  Zone.lean::zoneStepPair_below: 314/582 = 54%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_twoSteps_fields: 559/1039 = 54%
   Deterministic.lean::haltsAtStep  reproduces  Deterministic.lean::ComputesInTimeAndSpace: 64/119 = 54%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 100/186 = 54%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 100/186 = 54%
   ZoneRebalance.lean::zr_leftWalk_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 100/186 = 54%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 100/186 = 54%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_singleton_fields: 100/186 = 54%
   Finite.lean::output_prefix  reproduces  Universal.lean::timedCut_live_before: 65/121 = 54%
   AlphabetReduction.lean::arReadCfg_run  reproduces  AlphabetReduction.lean::arWriteCfg_run: 94/175 = 54%
   ZoneRebalance.lean::zr_rightReturnRow  reproduces  ZoneRebalance.lean::zr_rightLeftRow: 88/164 = 54%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_leftMove_fields: 797/1487 = 54%
   Zone.lean::zoneShiftIndex_extend  reproduces  Zone.lean::zoneShiftIndex_extend_of_lt: 179/334 = 54%
   ZoneRebalance.lean::zr_writeHalves_post  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 75/140 = 54%
   ZoneRebalance.lean::zr_rightReturn_post  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 75/140 = 54%
   ZoneRebalance.lean::zr_rightReturn_bounds  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 75/140 = 54%
   ZoneRebalance.lean::zr_rightLeft_post  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 75/140 = 54%
   ZoneRebalance.lean::zr_rightLeft_fields  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 75/140 = 54%
   ZoneRebalance.lean::zr_extend_fields  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 75/140 = 54%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedCut_skip_unary: 671/1254 = 54%
   TCSlib/Complexity/TuringMachine/Build/Seam.lean::seamCompTM_runFrom_left  reproduces  Simulation.lean::bufferedFirstCfg_run: 122/228 = 54%
   ZoneRebalance.lean::zr_fpG8  reproduces  ZoneRebalance.lean::zr_fpG2: 481/899 = 54%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Traj.seq  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::Frames.seq: 163/305 = 53%
   ZoneRebalance.lean::zr_writeHalves_post  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 101/189 = 53%
   TwoTapes.lean::tt_D_level  reproduces  TwoTapes.lean::tt_D_inv: 381/713 = 53%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_body_post: 296/554 = 53%
   ZoneRebalance.lean::zr_countClearContract  reproduces  ZoneRebalance.lean::zr_leftPassContract: 234/438 = 53%
   Basic.lean::Contract  reproduces  Basic.lean::RoundContract: 302/566 = 53%
   ZoneRebalance.lean::zr_leftPassContract  reproduces  ZoneRebalance.lean::zr_shortContract: 264/495 = 53%
   ZoneRebalance.lean::zr_scan_round  reproduces  ZoneRebalance.lean::zr_scanPin_pre: 113/212 = 53%
   ZoneRebalance.lean::zr_px_iter  reproduces  ZoneRebalance.lean::zr_pxFold_id: 65/122 = 53%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_body_bounds: 263/494 = 53%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_leftMove_link₁: 165/310 = 53%
   ZoneRebalance.lean::zr_fpG7  reproduces  ZoneRebalance.lean::zr_fpG9: 365/686 = 53%
   ZoneRebalance.lean::zr_fp6  reproduces  ZoneRebalance.lean::zr_fp3: 184/346 = 53%
   Universal.lean::timed_output_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timed_clock_back  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_unary_copy  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_table_rewind  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_unary  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_skip_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_read_fixed  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedFrame_run: 67/126 = 53%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_test_post: 311/585 = 53%
   ZoneRebalance.lean::zr_countClearContract  reproduces  ZoneRebalance.lean::zr_scanContract: 271/510 = 53%
   ZoneRebalance.lean::zr_twoSteps_fields  reproduces  ZoneRebalance.lean::zr_pinRe_ofSeg: 77/145 = 53%
   ZoneRebalance.lean::zr_goShift_step  reproduces  ZoneRebalance.lean::zr_PinStep_seq': 69/130 = 53%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_extend_pre: 96/181 = 53%
   ZoneRebalance.lean::zr_rightSeek_back_pre  reproduces  ZoneRebalance.lean::zr_rightSeekBack_ruler_pre: 272/513 = 53%
   ZoneRebalance.lean::zr_rulerStep_walk_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 89/168 = 53%
   ZoneRebalance.lean::zr_scan_round  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 109/206 = 53%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 109/206 = 53%
   ZoneRebalance.lean::zr_leftWalk_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 100/189 = 53%
   ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 100/189 = 53%
   ZoneRebalance.lean::zr_adjustedWalk_back_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 100/189 = 53%
   ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 100/189 = 53%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_body_post: 293/554 = 53%
   AlphabetReduction.lean::arEmission_in_image  reproduces  Universal.lean::timedPrefix_live: 101/191 = 53%
   ZoneRebalance.lean::zr_loop_round  reproduces  ZoneRebalance.lean::zr_rightPass_pre: 74/140 = 53%
   SingleTape.lean::dg_turn_without_growth  reproduces  SingleTape.lean::dg_end_without_growth: 241/456 = 53%
   ZoneRebalance.lean::zr_fpG8  reproduces  ZoneRebalance.lean::zr_fpG6: 619/1172 = 53%
   ZoneRebalance.lean::zr_p3Arm_step  reproduces  ZoneRebalance.lean::zr_p4Arm_step: 791/1498 = 53%
   ZoneTape.lean::zoneOwner_beyond  reproduces  ZoneTape.lean::zoneOwner_sep: 105/199 = 53%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightReturn_pre: 96/182 = 53%
   Universal.lean::timed_clock_success  reproduces  Universal.lean::timed_clock_timeout: 513/975 = 53%
   Embed.lean::embedSilentTM_spaceUsedByTape_cap  reproduces  Embed.lean::embedSilentTM_visitedByTapeHead: 141/268 = 53%
   ZoneRebalance.lean::zr_rightLeft_post  reproduces  ZoneRebalance.lean::zr_body_post: 291/554 = 53%
   ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_leftWalk_pre: 188/358 = 53%
   ZoneRebalance.lean::zr_rightReturn_post  reproduces  ZoneRebalance.lean::zr_return_post: 242/461 = 52%
   ZoneRebalance.lean::zr_rightLeft_post  reproduces  ZoneRebalance.lean::zr_return_post: 242/461 = 52%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 108/206 = 52%
   ZoneRebalance.lean::zr_rightReturn_link  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 108/206 = 52%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 88/168 = 52%
   ZoneRebalance.lean::zr_hmSc1  reproduces  ZoneRebalance.lean::zr_hmGat: 4774/9115 = 52%
   ZoneRebalance.lean::zr_ccPin_step  reproduces  ZoneRebalance.lean::zr_scanPin_step: 626/1196 = 52%
   Universal.lean::timedCut_initial_skip  reproduces  Universal.lean::timedCut_skip_fixed: 369/705 = 52%
   ZoneRebalance.lean::zr_scanLoop_segment  reproduces  ZoneRebalance.lean::zr_hm_pos: 68/130 = 52%
   StepBlockForward.lean::forwardLoopCfg  reproduces  Simulation.lean::rightCfg: 68/130 = 52%
   StepBlockForward.lean::forwardLoopCfg  reproduces  Simulation.lean::leftCfg: 68/130 = 52%
   ZoneRebalance.lean::zr_lfields  reproduces  ZoneRebalance.lean::zr_inV_lengths: 239/457 = 52%
   ZoneRebalance.lean::zr_fpG6  reproduces  ZoneRebalance.lean::zr_fpG2: 470/899 = 52%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_countClear_fields: 1003/1920 = 52%
   ZoneRebalance.lean::zr_rbPass  reproduces  ZoneRebalance.lean::zr_lbPass: 455/871 = 52%
   ZoneRebalance.lean::zr_p3Arm_step  reproduces  ZoneRebalance.lean::zr_woLead_step: 339/649 = 52%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_body_bounds: 258/494 = 52%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_body_bounds: 258/494 = 52%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 294/563 = 52%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_rightLeftFinal_link: 240/460 = 52%
   ZoneRebalance.lean::zr_cNxt_iter  reproduces  ZoneRebalance.lean::zr_iterate_step: 73/140 = 52%
   Universal.lean::timed_input_layout  reproduces  Universal.lean::timedClockPrefix_length: 73/140 = 52%
   ZoneRebalance.lean::zr_col_zone  reproduces  ZoneRebalance.lean::zr_lcol: 304/584 = 52%
   ZoneRebalance.lean::zr_rightReturn_link  reproduces  ZoneRebalance.lean::zr_return_time: 77/148 = 52%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_twoStepsContract: 207/398 = 52%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_test_post: 304/585 = 52%
   ZoneRebalance.lean::zr_pinBackContract  reproduces  ZoneRebalance.lean::zr_pinCopyContract: 80/154 = 52%
   ZoneRebalance.lean::zr_rightRuler_write_pre  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 107/206 = 52%
   ZoneRebalance.lean::zr_scanBody_fields  reproduces  ZoneRebalance.lean::zr_adjustedWalk_post: 363/699 = 52%
   ZoneRebalance.lean::zr_leftMoveContract  reproduces  ZoneRebalance.lean::zr_returnContract: 195/376 = 52%
   ZoneRebalance.lean::zr_inV_lengths  reproduces  ZoneRebalance.lean::zr_lfields: 239/461 = 52%
   ZoneRebalance.lean::zr_return_bounds  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 87/168 = 52%
   ZoneRebalance.lean::zr_leftWalk_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 87/168 = 52%
   ZoneRebalance.lean::zr_innerCopy_adjusted_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 87/168 = 52%
   ZoneRebalance.lean::zr_adjustedWalk_back_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 87/168 = 52%
   ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 87/168 = 52%
   ZoneRebalance.lean::zr_pass_step  reproduces  ZoneRebalance.lean::zr_pinRe_ofSeg: 75/145 = 52%
   ZoneRebalance.lean::zr_dnG_pre  reproduces  ZoneRebalance.lean::zr_popG_pre: 106/205 = 52%
   ZoneRebalance.lean::zr_leftMove_fields  reproduces  ZoneRebalance.lean::zr_twoSteps_fields: 537/1039 = 52%
   ZoneRebalance.lean::zr_rightSeekBack_ruler_pre  reproduces  ZoneRebalance.lean::zr_rightLeft_pre: 96/186 = 52%
   ZoneRebalance.lean::zr_inSeg  reproduces  ZoneRebalance.lean::zr_outSeg: 13224/25666 = 52%
   ZoneRebalance.lean::zr_writeHalves_post  reproduces  ZoneRebalance.lean::zr_leftMove_pre: 106/206 = 51%
   ZoneRebalance.lean::zr_pop_iter  reproduces  ZoneRebalance.lean::zr_lb_iter: 107/208 = 51%
   ZoneRebalance.lean::zr_adjustedWalk_back_pre  reproduces  ZoneRebalance.lean::zr_leftWalk_pre: 184/358 = 51%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_leftWalk_pre: 184/358 = 51%
   ZoneRebalance.lean::zr_shiftIn_tape  reproduces  ZoneRebalance.lean::zr_slot_track: 210/409 = 51%
   AlphabetReduction.lean::arTail_update  reproduces  AlphabetReduction.lean::arBuffer_update: 78/152 = 51%
   ZoneRebalance.lean::zr_scan_fields  reproduces  ZoneRebalance.lean::zr_rightLeftFinal_link: 236/460 = 51%
   Simulation.lean::timed_rewind  reproduces  Simulation.lean::rewind_from_any: 239/466 = 51%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_rightSeekBack_post: 473/923 = 51%
   ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_adjustedWalk_post: 358/699 = 51%
   ZoneRebalance.lean::zr_shiftOut_off  reproduces  ZoneRebalance.lean::zr_shiftIn_off: 85/166 = 51%
   ZoneRebalance.lean::zr_hmSc2  reproduces  ZoneRebalance.lean::zr_prSeg: 2356/4602 = 51%
   ZoneRebalance.lean::zr_p3Tau_le  reproduces  ZoneRebalance.lean::zr_p4Tau_le: 88/172 = 51%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_return_bounds: 288/563 = 51%
   SingleTape.lean::dg_turn_with_growth  reproduces  SingleTape.lean::dg_end_without_growth: 233/456 = 51%
   ZoneRebalance.lean::zr_leftWriteContract  reproduces  ZoneRebalance.lean::zr_returnContract: 192/376 = 51%
   ZoneRebalance.lean::zr_iterate_step  reproduces  ZoneRebalance.lean::zr_cNxt_iter: 73/143 = 51%
   ZoneRebalance.lean::zr_rbTau_le  reproduces  ZoneRebalance.lean::zr_p1Tau_le: 99/194 = 51%
   ZoneRebalance.lean::zr_hmSc1  reproduces  ZoneRebalance.lean::zr_hmSc2: 4591/8999 = 51%
   ZoneRebalance.lean::zr_hmSeg_spec  reproduces  ZoneRebalance.lean::zr_retSeg_spec: 77/151 = 51%
   ZoneRebalance.lean::zr_rightSeekBack_post  reproduces  ZoneRebalance.lean::zr_adjustedBack_post: 528/1036 = 51%
   ZoneRebalance.lean::zr_rightReturn_post  reproduces  ZoneRebalance.lean::zr_body_post: 282/554 = 51%
   ZoneRebalance.lean::zr_shiftOut_tape  reproduces  ZoneRebalance.lean::zr_slot_track: 208/409 = 51%
   ZoneRebalance.lean::zr_leftWrite_fields  reproduces  ZoneRebalance.lean::zr_leftMove_fields: 756/1487 = 51%
   ZoneRebalance.lean::zr_fp7  reproduces  ZoneRebalance.lean::zr_fp9: 153/301 = 51%
   ZoneRebalance.lean::zr_rightPass_pre  reproduces  ZoneRebalance.lean::zr_rightRuler_pre: 96/189 = 51%
   TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::branch  reproduces  TCSlib/Complexity/TuringMachine/Build/Contract/Seam.lean::seq: 1194/2353 = 51%
   ZoneRebalance.lean::zr_loop_home_word  reproduces  ZoneRebalance.lean::zr_loop_home_test: 137/270 = 51%
   ZoneRebalance.lean::zr_shortPin_step  reproduces  ZoneRebalance.lean::zr_scanPin_step: 606/1196 = 51%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_pinRe_step: 152/300 = 51%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_pinRe_step: 152/300 = 51%
   ZoneRebalance.lean::zr_rightWord_word  reproduces  ZoneRebalance.lean::zr_loop_home_word: 121/239 = 51%
   ZoneRebalance.lean::zr_writeHalves_post  reproduces  ZoneRebalance.lean::zr_test_post: 296/585 = 51%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_test_post: 296/585 = 51%
   ZoneRebalance.lean::zr_test_post  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 85/168 = 51%
   ZoneRebalance.lean::zr_adjustedBack_copy_pre  reproduces  ZoneRebalance.lean::zr_leftWalk_pre: 181/358 = 51%
   ZoneRebalance.lean::zr_pinRe_step  reproduces  ZoneRebalance.lean::zr_singleton_fields: 94/186 = 51%
   ZoneRebalance.lean::zr_leftPassContract  reproduces  ZoneRebalance.lean::zr_returnContract: 190/376 = 51%
   ZoneRebalance.lean::zr_fpG3  reproduces  ZoneRebalance.lean::zr_fpG4: 300/594 = 51%
   ZoneRebalance.lean::zr_hmContract_step  reproduces  ZoneRebalance.lean::zr_hmSeg_spec: 62/123 = 50%
   Universal.lean::timedCut_count_run  reproduces  Universal.lean::timedCut_skip_fixed: 355/705 = 50%
   ZoneRebalance.lean::zr_rightRulerContract  reproduces  ZoneRebalance.lean::zr_rightSeekBackContract: 75/149 = 50%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_pass_step: 227/451 = 50%
   ZoneRebalance.lean::zr_lb_home  reproduces  ZoneRebalance.lean::zr_rb_valid: 81/161 = 50%
   ZoneTape.lean::zonedTape_right_sep  reproduces  ZoneTape.lean::zonedTape_right: 92/183 = 50%
   Universal.lean::timedCapture_start  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   AlphabetReduction.lean::alphabet_reduction_run  reproduces  Universal.lean::timedPrefix_live: 96/191 = 50%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_fields: 764/1521 = 50%
   SymbolLift.lean::MultiTapeTM.liftSymbols_step_over  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_step: 536/1068 = 50%
   ZoneRebalance.lean::zr_rightRuler_post  reproduces  ZoneRebalance.lean::zr_rulerCopy_skip_pre: 152/303 = 50%
   SingleTape.lean::sweep_grow_right_block  reproduces  SingleTape.lean::sweep_grow_left_block: 343/684 = 50%
   ZoneRebalance.lean::zr_adjustedBack_post  reproduces  ZoneRebalance.lean::zr_innerCopy_adjusted_pre: 303/605 = 50%
   ZoneRebalance.lean::zr_hmSc1  reproduces  ZoneRebalance.lean::zr_prSeg: 2303/4602 = 50%
   ZoneRebalance.lean::zr_goRoom  reproduces  ZoneRebalance.lean::zr_grdIn: 120/240 = 50%
   ZoneRebalance.lean::zr_leftPass_fields  reproduces  ZoneRebalance.lean::zr_scanPin_pre: 106/212 = 50%
   ZoneRebalance.lean::zr_final_fields  reproduces  ZoneRebalance.lean::zr_scanPin_pre: 106/212 = 50%
   Universal.lean::timedFrame_apply  reproduces  Simulation.lean::leftCfg_apply: 94/188 = 50%
   ZoneRebalance.lean::zr_countClear_fields  reproduces  ZoneRebalance.lean::zr_leftWrite_pre: 84/168 = 50%
   ZoneTape.lean::zonedTape_left  reproduces  ZoneTape.lean::zonedTape_right_sep: 79/158 = 50%
   ZoneRebalance.lean::zr_pinWalkContract  reproduces  ZoneRebalance.lean::zr_pinCopyContract: 77/154 = 50%
   ZoneRebalance.lean::zr_short_fields  reproduces  ZoneRebalance.lean::zr_return_time: 74/148 = 50%
   ZoneRebalance.lean::zr_rightPass_time_le  reproduces  ZoneRebalance.lean::zr_extend_time_le: 70/140 = 50%
   ZoneRebalance.lean::zr_scratchBackContract  reproduces  ZoneRebalance.lean::zr_pinBackContract: 68/136 = 50%
   ZoneRebalance.lean::zr_hmArm_step  reproduces  ZoneRebalance.lean::zr_PinStep_seq': 65/130 = 50%
   StateRenaming.lean::MultiTapeTM.relabelState_spaceUsed  reproduces  SymbolLift.lean::MultiTapeTM.liftSymbols_spaceUsed: 63/126 = 50%
   Universal.lean::timedClockCfg  reproduces  Universal.lean::timed_laneCfg: 60/120 = 50%

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/G5LandAx.lean.txt =====

import TCSlib.Complexity.TuringMachine

/-! The maintainer's axiom prints for G5's landing (#211, round 2), on `oleans-lg7`. -/

#print axioms Turing.FinTM.two_work_tapes_run
#print axioms Turing.FinTM.two_work_tapes_binary
#print axioms Turing.universal_TlogT

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/G5LandAx.out =====

'Turing.FinTM.two_work_tapes_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.two_work_tapes_binary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.universal_TlogT' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesCtl_sealed.lean.txt =====

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.ZoneStep
import TCSlib.Complexity.TuringMachine.SymbolLift

/-! Rule-10 controls for TwoTapes (sealed): 44 definitions, 3 of them `@[simp]`. -/

open Lean Elab Command Meta in
elab "#ctl_rfl " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let goal ← mkEq (mkConst n (ci.levelParams.map Level.param)) value
        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} rfl {n}"

open Lean Elab Command Meta in
elab "#ctl_eqn " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ok ← liftTermElabM do
    try
      let some eqs ← getEqnsFor? n | return false
      let ty := (← getConstInfo eqs[0]!).type
      let ty ← instantiateForall ty #[]
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType (← `(by intros; rfl)) ty
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} eqn {n}"

open Lean Elab Command Meta in
elab "#ctl_simp " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let c := mkConst n (ci.levelParams.map Level.param)
        let goal ← forallTelescopeReducing ci.type fun xs _ => do
          mkForallFVars xs (← mkEq (mkAppN c xs) (mkAppN value xs).headBeta)
        let proof ← Term.elabTermEnsuringType (← `(by intros; simp)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} simp {n}"



section Controls

attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.FinTM.ComputesFunInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.spaceUsed
  Turing.MultiTapeTM.spaceUsedByTape
  Turing.MultiTapeTM.visitedByTapeHead
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init
  Turing.MultiTapeTM.step
  Turing.Action.apply
  Turing.Cfg.inputSymbol
  Turing.Cfg.workTapeSymbols
  Turing.moveInputPos
  Turing.embedEmitTM
  Turing.embedEmitCfg
  Turing.zoneRowPre
  Turing.zoneRebalanceIndex
  Turing.zoneRebalanceData
  Turing.zoneExtendData
  Turing.zoneTrackStepData
  Turing.zonedTape
  Turing.zoneHomeWrite
  Turing.zoneTrackTape
  Turing.zoneShiftIndex
  Turing.zoneRebalance
  Turing.zoneCascade
  Turing.ZoneContents.extend
  Turing.ZoneContents.words
  Turing.zoneCapacity
  Turing.zoneCellOfCell
  Turing.Contract.inPhase
  Turing.Contract.zero
  Turing.Contract.Positive
  Turing.Segment
  Turing.HeadBox
  Turing.Cfg.bindState
  Turing.Cfg.mapState
  Turing.phaseHostTM
  Turing.ZoneContents.empty
  Turing.zoneCascadeLeft
  Turing.zoneCascadeRight
  Turing.zoneStart
  Turing.Cfg.liftSymbols
attribute [-simp] Turing.MultiTapeTM.initCfg Turing.Cfg.init Turing.Action.apply

#ctl_rfl Turing.FinTM.ComputesInTime
#ctl_rfl Turing.FinTM.ComputesFunInTime
#ctl_rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_rfl Turing.MultiTapeTM.spaceUsed
#ctl_rfl Turing.MultiTapeTM.spaceUsedByTape
#ctl_rfl Turing.MultiTapeTM.visitedByTapeHead
#ctl_rfl Turing.MultiTapeTM.runFrom
#ctl_rfl Turing.MultiTapeTM.initCfg
#ctl_rfl Turing.Cfg.init
#ctl_rfl Turing.MultiTapeTM.step
#ctl_rfl Turing.Action.apply
#ctl_rfl Turing.Cfg.inputSymbol
#ctl_rfl Turing.Cfg.workTapeSymbols
#ctl_rfl Turing.moveInputPos
#ctl_rfl Turing.embedEmitTM
#ctl_rfl Turing.embedEmitCfg
#ctl_rfl Turing.zoneRowPre
#ctl_rfl Turing.zoneRebalanceIndex
#ctl_rfl Turing.zoneRebalanceData
#ctl_rfl Turing.zoneExtendData
#ctl_rfl Turing.zoneTrackStepData
#ctl_rfl Turing.zonedTape
#ctl_rfl Turing.zoneHomeWrite
#ctl_rfl Turing.zoneTrackTape
#ctl_rfl Turing.zoneShiftIndex
#ctl_rfl Turing.zoneRebalance
#ctl_rfl Turing.zoneCascade
#ctl_rfl Turing.ZoneContents.extend
#ctl_rfl Turing.ZoneContents.words
#ctl_rfl Turing.zoneCapacity
#ctl_rfl Turing.zoneCellOfCell
#ctl_rfl Turing.Contract.inPhase
#ctl_rfl Turing.Contract.zero
#ctl_rfl Turing.Contract.Positive
#ctl_rfl Turing.Segment
#ctl_rfl Turing.HeadBox
#ctl_rfl Turing.Cfg.bindState
#ctl_rfl Turing.Cfg.mapState
#ctl_rfl Turing.phaseHostTM
#ctl_rfl Turing.ZoneContents.empty
#ctl_rfl Turing.zoneCascadeLeft
#ctl_rfl Turing.zoneCascadeRight
#ctl_rfl Turing.zoneStart
#ctl_rfl Turing.Cfg.liftSymbols
#ctl_eqn Turing.FinTM.ComputesInTime
#ctl_eqn Turing.FinTM.ComputesFunInTime
#ctl_eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_eqn Turing.MultiTapeTM.spaceUsed
#ctl_eqn Turing.MultiTapeTM.spaceUsedByTape
#ctl_eqn Turing.MultiTapeTM.visitedByTapeHead
#ctl_eqn Turing.MultiTapeTM.runFrom
#ctl_eqn Turing.MultiTapeTM.initCfg
#ctl_eqn Turing.Cfg.init
#ctl_eqn Turing.MultiTapeTM.step
#ctl_eqn Turing.Action.apply
#ctl_eqn Turing.Cfg.inputSymbol
#ctl_eqn Turing.Cfg.workTapeSymbols
#ctl_eqn Turing.moveInputPos
#ctl_eqn Turing.embedEmitTM
#ctl_eqn Turing.embedEmitCfg
#ctl_eqn Turing.zoneRowPre
#ctl_eqn Turing.zoneRebalanceIndex
#ctl_eqn Turing.zoneRebalanceData
#ctl_eqn Turing.zoneExtendData
#ctl_eqn Turing.zoneTrackStepData
#ctl_eqn Turing.zonedTape
#ctl_eqn Turing.zoneHomeWrite
#ctl_eqn Turing.zoneTrackTape
#ctl_eqn Turing.zoneShiftIndex
#ctl_eqn Turing.zoneRebalance
#ctl_eqn Turing.zoneCascade
#ctl_eqn Turing.ZoneContents.extend
#ctl_eqn Turing.ZoneContents.words
#ctl_eqn Turing.zoneCapacity
#ctl_eqn Turing.zoneCellOfCell
#ctl_eqn Turing.Contract.inPhase
#ctl_eqn Turing.Contract.zero
#ctl_eqn Turing.Contract.Positive
#ctl_eqn Turing.Segment
#ctl_eqn Turing.HeadBox
#ctl_eqn Turing.Cfg.bindState
#ctl_eqn Turing.Cfg.mapState
#ctl_eqn Turing.phaseHostTM
#ctl_eqn Turing.ZoneContents.empty
#ctl_eqn Turing.zoneCascadeLeft
#ctl_eqn Turing.zoneCascadeRight
#ctl_eqn Turing.zoneStart
#ctl_eqn Turing.Cfg.liftSymbols
#ctl_simp Turing.MultiTapeTM.initCfg
#ctl_simp Turing.Cfg.init
#ctl_simp Turing.Action.apply

end Controls

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesCtl_sealed.out =====

CONTROL_FAIL rfl Turing.FinTM.ComputesInTime
CONTROL_FAIL rfl Turing.FinTM.ComputesFunInTime
CONTROL_FAIL rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_FAIL rfl Turing.MultiTapeTM.spaceUsed
CONTROL_FAIL rfl Turing.MultiTapeTM.spaceUsedByTape
CONTROL_FAIL rfl Turing.MultiTapeTM.visitedByTapeHead
CONTROL_FAIL rfl Turing.MultiTapeTM.runFrom
CONTROL_FAIL rfl Turing.MultiTapeTM.initCfg
CONTROL_FAIL rfl Turing.Cfg.init
CONTROL_FAIL rfl Turing.MultiTapeTM.step
CONTROL_FAIL rfl Turing.Action.apply
CONTROL_FAIL rfl Turing.Cfg.inputSymbol
CONTROL_FAIL rfl Turing.Cfg.workTapeSymbols
CONTROL_FAIL rfl Turing.moveInputPos
CONTROL_FAIL rfl Turing.embedEmitTM
CONTROL_FAIL rfl Turing.embedEmitCfg
CONTROL_FAIL rfl Turing.zoneRowPre
CONTROL_FAIL rfl Turing.zoneRebalanceIndex
CONTROL_FAIL rfl Turing.zoneRebalanceData
CONTROL_FAIL rfl Turing.zoneExtendData
CONTROL_FAIL rfl Turing.zoneTrackStepData
CONTROL_FAIL rfl Turing.zonedTape
CONTROL_FAIL rfl Turing.zoneHomeWrite
CONTROL_FAIL rfl Turing.zoneTrackTape
CONTROL_FAIL rfl Turing.zoneShiftIndex
CONTROL_FAIL rfl Turing.zoneRebalance
CONTROL_FAIL rfl Turing.zoneCascade
CONTROL_FAIL rfl Turing.ZoneContents.extend
CONTROL_FAIL rfl Turing.ZoneContents.words
CONTROL_FAIL rfl Turing.zoneCapacity
CONTROL_FAIL rfl Turing.zoneCellOfCell
CONTROL_FAIL rfl Turing.Contract.inPhase
CONTROL_FAIL rfl Turing.Contract.zero
CONTROL_FAIL rfl Turing.Contract.Positive
CONTROL_FAIL rfl Turing.Segment
CONTROL_FAIL rfl Turing.HeadBox
CONTROL_FAIL rfl Turing.Cfg.bindState
CONTROL_FAIL rfl Turing.Cfg.mapState
CONTROL_FAIL rfl Turing.phaseHostTM
CONTROL_FAIL rfl Turing.ZoneContents.empty
CONTROL_FAIL rfl Turing.zoneCascadeLeft
CONTROL_FAIL rfl Turing.zoneCascadeRight
CONTROL_FAIL rfl Turing.zoneStart
CONTROL_FAIL rfl Turing.Cfg.liftSymbols
CONTROL_FAIL eqn Turing.FinTM.ComputesInTime
CONTROL_FAIL eqn Turing.FinTM.ComputesFunInTime
CONTROL_FAIL eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_FAIL eqn Turing.MultiTapeTM.spaceUsed
CONTROL_FAIL eqn Turing.MultiTapeTM.spaceUsedByTape
CONTROL_FAIL eqn Turing.MultiTapeTM.visitedByTapeHead
CONTROL_FAIL eqn Turing.MultiTapeTM.runFrom
CONTROL_FAIL eqn Turing.MultiTapeTM.initCfg
CONTROL_FAIL eqn Turing.Cfg.init
CONTROL_FAIL eqn Turing.MultiTapeTM.step
CONTROL_FAIL eqn Turing.Action.apply
CONTROL_FAIL eqn Turing.Cfg.inputSymbol
CONTROL_FAIL eqn Turing.Cfg.workTapeSymbols
CONTROL_FAIL eqn Turing.moveInputPos
CONTROL_FAIL eqn Turing.embedEmitTM
CONTROL_FAIL eqn Turing.embedEmitCfg
CONTROL_FAIL eqn Turing.zoneRowPre
CONTROL_FAIL eqn Turing.zoneRebalanceIndex
CONTROL_FAIL eqn Turing.zoneRebalanceData
CONTROL_FAIL eqn Turing.zoneExtendData
CONTROL_FAIL eqn Turing.zoneTrackStepData
CONTROL_FAIL eqn Turing.zonedTape
CONTROL_FAIL eqn Turing.zoneHomeWrite
CONTROL_FAIL eqn Turing.zoneTrackTape
CONTROL_FAIL eqn Turing.zoneShiftIndex
CONTROL_FAIL eqn Turing.zoneRebalance
CONTROL_FAIL eqn Turing.zoneCascade
CONTROL_FAIL eqn Turing.ZoneContents.extend
CONTROL_FAIL eqn Turing.ZoneContents.words
CONTROL_FAIL eqn Turing.zoneCapacity
CONTROL_FAIL eqn Turing.zoneCellOfCell
CONTROL_FAIL eqn Turing.Contract.inPhase
CONTROL_FAIL eqn Turing.Contract.zero
CONTROL_FAIL eqn Turing.Contract.Positive
CONTROL_FAIL eqn Turing.Segment
CONTROL_FAIL eqn Turing.HeadBox
CONTROL_FAIL eqn Turing.Cfg.bindState
CONTROL_FAIL eqn Turing.Cfg.mapState
CONTROL_FAIL eqn Turing.phaseHostTM
CONTROL_FAIL eqn Turing.ZoneContents.empty
CONTROL_FAIL eqn Turing.zoneCascadeLeft
CONTROL_FAIL eqn Turing.zoneCascadeRight
CONTROL_FAIL eqn Turing.zoneStart
CONTROL_FAIL eqn Turing.Cfg.liftSymbols
CONTROL_FAIL simp Turing.MultiTapeTM.initCfg
CONTROL_FAIL simp Turing.Cfg.init
CONTROL_FAIL simp Turing.Action.apply

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesCtl_unsealed.lean.txt =====

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.ZoneStep
import TCSlib.Complexity.TuringMachine.SymbolLift

/-! Rule-10 controls for TwoTapes (unsealed): 44 definitions, 3 of them `@[simp]`. -/

open Lean Elab Command Meta in
elab "#ctl_rfl " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let goal ← mkEq (mkConst n (ci.levelParams.map Level.param)) value
        let proof ← Term.elabTermEnsuringType (← `(by rfl)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} rfl {n}"

open Lean Elab Command Meta in
elab "#ctl_eqn " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ok ← liftTermElabM do
    try
      let some eqs ← getEqnsFor? n | return false
      let ty := (← getConstInfo eqs[0]!).type
      let ty ← instantiateForall ty #[]
      Term.withoutErrToSorry do
        let proof ← Term.elabTermEnsuringType (← `(by intros; rfl)) ty
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} eqn {n}"

open Lean Elab Command Meta in
elab "#ctl_simp " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "not a definition: {n}"
  let ok ← liftTermElabM do
    try
      Term.withoutErrToSorry do
        let c := mkConst n (ci.levelParams.map Level.param)
        let goal ← forallTelescopeReducing ci.type fun xs _ => do
          mkForallFVars xs (← mkEq (mkAppN c xs) (mkAppN value xs).headBeta)
        let proof ← Term.elabTermEnsuringType (← `(by intros; simp)) goal
        Term.synthesizeSyntheticMVarsNoPostponing
        return !(← instantiateMVars proof).hasSorry
    catch _ => return false
  logInfo m!"{if ok then "CONTROL_PASS" else "CONTROL_FAIL"} simp {n}"



section Controls


#ctl_rfl Turing.FinTM.ComputesInTime
#ctl_rfl Turing.FinTM.ComputesFunInTime
#ctl_rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_rfl Turing.MultiTapeTM.spaceUsed
#ctl_rfl Turing.MultiTapeTM.spaceUsedByTape
#ctl_rfl Turing.MultiTapeTM.visitedByTapeHead
#ctl_rfl Turing.MultiTapeTM.runFrom
#ctl_rfl Turing.MultiTapeTM.initCfg
#ctl_rfl Turing.Cfg.init
#ctl_rfl Turing.MultiTapeTM.step
#ctl_rfl Turing.Action.apply
#ctl_rfl Turing.Cfg.inputSymbol
#ctl_rfl Turing.Cfg.workTapeSymbols
#ctl_rfl Turing.moveInputPos
#ctl_rfl Turing.embedEmitTM
#ctl_rfl Turing.embedEmitCfg
#ctl_rfl Turing.zoneRowPre
#ctl_rfl Turing.zoneRebalanceIndex
#ctl_rfl Turing.zoneRebalanceData
#ctl_rfl Turing.zoneExtendData
#ctl_rfl Turing.zoneTrackStepData
#ctl_rfl Turing.zonedTape
#ctl_rfl Turing.zoneHomeWrite
#ctl_rfl Turing.zoneTrackTape
#ctl_rfl Turing.zoneShiftIndex
#ctl_rfl Turing.zoneRebalance
#ctl_rfl Turing.zoneCascade
#ctl_rfl Turing.ZoneContents.extend
#ctl_rfl Turing.ZoneContents.words
#ctl_rfl Turing.zoneCapacity
#ctl_rfl Turing.zoneCellOfCell
#ctl_rfl Turing.Contract.inPhase
#ctl_rfl Turing.Contract.zero
#ctl_rfl Turing.Contract.Positive
#ctl_rfl Turing.Segment
#ctl_rfl Turing.HeadBox
#ctl_rfl Turing.Cfg.bindState
#ctl_rfl Turing.Cfg.mapState
#ctl_rfl Turing.phaseHostTM
#ctl_rfl Turing.ZoneContents.empty
#ctl_rfl Turing.zoneCascadeLeft
#ctl_rfl Turing.zoneCascadeRight
#ctl_rfl Turing.zoneStart
#ctl_rfl Turing.Cfg.liftSymbols
#ctl_eqn Turing.FinTM.ComputesInTime
#ctl_eqn Turing.FinTM.ComputesFunInTime
#ctl_eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
#ctl_eqn Turing.MultiTapeTM.spaceUsed
#ctl_eqn Turing.MultiTapeTM.spaceUsedByTape
#ctl_eqn Turing.MultiTapeTM.visitedByTapeHead
#ctl_eqn Turing.MultiTapeTM.runFrom
#ctl_eqn Turing.MultiTapeTM.initCfg
#ctl_eqn Turing.Cfg.init
#ctl_eqn Turing.MultiTapeTM.step
#ctl_eqn Turing.Action.apply
#ctl_eqn Turing.Cfg.inputSymbol
#ctl_eqn Turing.Cfg.workTapeSymbols
#ctl_eqn Turing.moveInputPos
#ctl_eqn Turing.embedEmitTM
#ctl_eqn Turing.embedEmitCfg
#ctl_eqn Turing.zoneRowPre
#ctl_eqn Turing.zoneRebalanceIndex
#ctl_eqn Turing.zoneRebalanceData
#ctl_eqn Turing.zoneExtendData
#ctl_eqn Turing.zoneTrackStepData
#ctl_eqn Turing.zonedTape
#ctl_eqn Turing.zoneHomeWrite
#ctl_eqn Turing.zoneTrackTape
#ctl_eqn Turing.zoneShiftIndex
#ctl_eqn Turing.zoneRebalance
#ctl_eqn Turing.zoneCascade
#ctl_eqn Turing.ZoneContents.extend
#ctl_eqn Turing.ZoneContents.words
#ctl_eqn Turing.zoneCapacity
#ctl_eqn Turing.zoneCellOfCell
#ctl_eqn Turing.Contract.inPhase
#ctl_eqn Turing.Contract.zero
#ctl_eqn Turing.Contract.Positive
#ctl_eqn Turing.Segment
#ctl_eqn Turing.HeadBox
#ctl_eqn Turing.Cfg.bindState
#ctl_eqn Turing.Cfg.mapState
#ctl_eqn Turing.phaseHostTM
#ctl_eqn Turing.ZoneContents.empty
#ctl_eqn Turing.zoneCascadeLeft
#ctl_eqn Turing.zoneCascadeRight
#ctl_eqn Turing.zoneStart
#ctl_eqn Turing.Cfg.liftSymbols
#ctl_simp Turing.MultiTapeTM.initCfg
#ctl_simp Turing.Cfg.init
#ctl_simp Turing.Action.apply

end Controls

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesCtl_unsealed.out =====

CONTROL_PASS rfl Turing.FinTM.ComputesInTime
CONTROL_PASS rfl Turing.FinTM.ComputesFunInTime
CONTROL_PASS rfl Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_PASS rfl Turing.MultiTapeTM.spaceUsed
CONTROL_PASS rfl Turing.MultiTapeTM.spaceUsedByTape
CONTROL_PASS rfl Turing.MultiTapeTM.visitedByTapeHead
CONTROL_PASS rfl Turing.MultiTapeTM.runFrom
CONTROL_PASS rfl Turing.MultiTapeTM.initCfg
CONTROL_PASS rfl Turing.Cfg.init
CONTROL_PASS rfl Turing.MultiTapeTM.step
CONTROL_PASS rfl Turing.Action.apply
CONTROL_PASS rfl Turing.Cfg.inputSymbol
CONTROL_PASS rfl Turing.Cfg.workTapeSymbols
CONTROL_PASS rfl Turing.moveInputPos
CONTROL_PASS rfl Turing.embedEmitTM
CONTROL_PASS rfl Turing.embedEmitCfg
CONTROL_PASS rfl Turing.zoneRowPre
CONTROL_PASS rfl Turing.zoneRebalanceIndex
CONTROL_PASS rfl Turing.zoneRebalanceData
CONTROL_PASS rfl Turing.zoneExtendData
CONTROL_PASS rfl Turing.zoneTrackStepData
CONTROL_PASS rfl Turing.zonedTape
CONTROL_PASS rfl Turing.zoneHomeWrite
CONTROL_PASS rfl Turing.zoneTrackTape
CONTROL_PASS rfl Turing.zoneShiftIndex
CONTROL_PASS rfl Turing.zoneRebalance
CONTROL_PASS rfl Turing.zoneCascade
CONTROL_PASS rfl Turing.ZoneContents.extend
CONTROL_PASS rfl Turing.ZoneContents.words
CONTROL_PASS rfl Turing.zoneCapacity
CONTROL_PASS rfl Turing.zoneCellOfCell
CONTROL_PASS rfl Turing.Contract.inPhase
CONTROL_PASS rfl Turing.Contract.zero
CONTROL_PASS rfl Turing.Contract.Positive
CONTROL_PASS rfl Turing.Segment
CONTROL_PASS rfl Turing.HeadBox
CONTROL_PASS rfl Turing.Cfg.bindState
CONTROL_PASS rfl Turing.Cfg.mapState
CONTROL_PASS rfl Turing.phaseHostTM
CONTROL_PASS rfl Turing.ZoneContents.empty
CONTROL_PASS rfl Turing.zoneCascadeLeft
CONTROL_PASS rfl Turing.zoneCascadeRight
CONTROL_PASS rfl Turing.zoneStart
CONTROL_PASS rfl Turing.Cfg.liftSymbols
CONTROL_PASS eqn Turing.FinTM.ComputesInTime
CONTROL_PASS eqn Turing.FinTM.ComputesFunInTime
CONTROL_PASS eqn Turing.MultiTapeTM.ComputesInTimeAndSpace
CONTROL_PASS eqn Turing.MultiTapeTM.spaceUsed
CONTROL_PASS eqn Turing.MultiTapeTM.spaceUsedByTape
CONTROL_PASS eqn Turing.MultiTapeTM.visitedByTapeHead
CONTROL_PASS eqn Turing.MultiTapeTM.runFrom
CONTROL_PASS eqn Turing.MultiTapeTM.initCfg
CONTROL_PASS eqn Turing.Cfg.init
CONTROL_PASS eqn Turing.MultiTapeTM.step
CONTROL_PASS eqn Turing.Action.apply
CONTROL_PASS eqn Turing.Cfg.inputSymbol
CONTROL_PASS eqn Turing.Cfg.workTapeSymbols
CONTROL_PASS eqn Turing.moveInputPos
CONTROL_PASS eqn Turing.embedEmitTM
CONTROL_PASS eqn Turing.embedEmitCfg
CONTROL_PASS eqn Turing.zoneRowPre
CONTROL_PASS eqn Turing.zoneRebalanceIndex
CONTROL_PASS eqn Turing.zoneRebalanceData
CONTROL_PASS eqn Turing.zoneExtendData
CONTROL_PASS eqn Turing.zoneTrackStepData
CONTROL_PASS eqn Turing.zonedTape
CONTROL_PASS eqn Turing.zoneHomeWrite
CONTROL_PASS eqn Turing.zoneTrackTape
CONTROL_PASS eqn Turing.zoneShiftIndex
CONTROL_PASS eqn Turing.zoneRebalance
CONTROL_PASS eqn Turing.zoneCascade
CONTROL_PASS eqn Turing.ZoneContents.extend
CONTROL_PASS eqn Turing.ZoneContents.words
CONTROL_PASS eqn Turing.zoneCapacity
CONTROL_PASS eqn Turing.zoneCellOfCell
CONTROL_PASS eqn Turing.Contract.inPhase
CONTROL_PASS eqn Turing.Contract.zero
CONTROL_PASS eqn Turing.Contract.Positive
CONTROL_PASS eqn Turing.Segment
CONTROL_PASS eqn Turing.HeadBox
CONTROL_PASS eqn Turing.Cfg.bindState
CONTROL_PASS eqn Turing.Cfg.mapState
CONTROL_PASS eqn Turing.phaseHostTM
CONTROL_PASS eqn Turing.ZoneContents.empty
CONTROL_PASS eqn Turing.zoneCascadeLeft
CONTROL_PASS eqn Turing.zoneCascadeRight
CONTROL_PASS eqn Turing.zoneStart
CONTROL_PASS eqn Turing.Cfg.liftSymbols
CONTROL_PASS simp Turing.MultiTapeTM.initCfg
CONTROL_PASS simp Turing.Cfg.init
CONTROL_PASS simp Turing.Action.apply

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesSealed.lean.txt =====

/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.ZoneStep
import TCSlib.Complexity.TuringMachine.SymbolLift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included. With no work tapes
  there is nothing to fold: `M` runs on the two-tape host through the forwarding embedding
  `Turing.embedEmitTM`, beside two idle tapes.
* For `k ≥ 1` the simulator is built over the zone alphabet `Turing.ZoneSym k` (a binary symbol,
  or one cell holding a slot of every track), the formal counterpart of the book's alphabet of
  `k` parallel tracks with a buffer symbol, and is then made binary by the alphabet reduction
  `Turing.FinTM.alphabet_reduction_run` [AB09, Claim 1.5], which keeps the two work tapes and
  multiplies the time by a constant.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## Implementation notes

For `k ≥ 1` the simulator is a phase host (`Turing.phaseHostTM`) over `Turing.ZoneSym k` with two
work tapes: tape `0` carries `M`'s `k` work tapes as the tracks of one zoned tape
(`Turing.zonedTape`), every simulated head at the home cell, and tape `1` is scratch; the input
is read as `x.map Sum.inl`. One round simulates one step of `M`: a transition step reads the
home tuple and the input symbol, applies `M`'s transition, writes the new home symbols and emits
the encoded output; then each track runs one track step in the direction of its head move
(`Turing.exists_zoneTrackStepTM`: a rebalance at the scanned index, preceded by an extension of
the zones when the scan finds none), a stay taking no time. The rounds are chained as segments
(`Turing.Segment.iterate_seq`). Along the run every track represents the corresponding work tape
of `M` and is *full*: at each level `i` its two zones hold `2 · 2^i` cells together and the right
one holds `0`, `2^i` or `2 · 2^i`. The count of expensive steps uses side totals, the numbers of
cells in a track's right zones below a level: after a step of scanned index above `i` the levels
`0, …, i` are half full, so the next such step of the same track comes at least `2^i` rounds
later, and a zone `j ≥ 1` is rebalanced at most once every `2^(j-1)` steps, as in the sketch of
`Turing.FinTM.two_work_tapes_run`. An extension to level `ℓ` needs a head displacement of
`2^ℓ − 1`, so in a run of `T` live rounds every scanned index is at most `log₂ T + 1`, and
`Turing.sum_cost_le_of_count` sums the rounds' costs.

The file is long because it is one construction and its correctness proof: apart from a few
arithmetic facts, its lemmas are about the simulator's own definitions (its rounds, the
invariant along its run and its cost count), so a split would have to make these internals
public.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

attribute [local irreducible]
  Turing.FinTM.ComputesInTime
  Turing.FinTM.ComputesFunInTime
  Turing.MultiTapeTM.ComputesInTimeAndSpace
  Turing.MultiTapeTM.spaceUsed
  Turing.MultiTapeTM.spaceUsedByTape
  Turing.MultiTapeTM.visitedByTapeHead
  Turing.MultiTapeTM.runFrom
  Turing.MultiTapeTM.initCfg
  Turing.Cfg.init
  Turing.MultiTapeTM.step
  Turing.Action.apply
  Turing.Cfg.inputSymbol
  Turing.Cfg.workTapeSymbols
  Turing.moveInputPos
  Turing.embedEmitTM
  Turing.embedEmitCfg
  Turing.zoneRowPre
  Turing.zoneRebalanceIndex
  Turing.zoneRebalanceData
  Turing.zoneExtendData
  Turing.zoneTrackStepData
  Turing.zonedTape
  Turing.zoneHomeWrite
  Turing.zoneTrackTape
  Turing.zoneShiftIndex
  Turing.zoneRebalance
  Turing.zoneCascade
  Turing.ZoneContents.extend
  Turing.ZoneContents.words
  Turing.zoneCapacity
  Turing.zoneCellOfCell
  Turing.Contract.inPhase
  Turing.Contract.zero
  Turing.Contract.Positive
  Turing.Segment
  Turing.HeadBox
  Turing.Cfg.bindState
  Turing.Cfg.mapState
  Turing.phaseHostTM
  Turing.ZoneContents.empty
  Turing.zoneCascadeLeft
  Turing.zoneCascadeRight
  Turing.zoneStart
  Turing.Cfg.liftSymbols
attribute [-simp] Turing.MultiTapeTM.initCfg Turing.Cfg.init Turing.Action.apply

/-! ### The frame and the zero-tape case -/

/-- **Zero work tapes** [HS66; AB09, §1.7]: a binary machine `M` without work tapes has a binary
equivalent with two work tapes that reproduces each halting run of `t` steps within
`1 · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of `M`.

**Proof sketch.** Run `M` on the two-tape host through the forwarding embedding
`Turing.embedEmitTM` along the empty selection `Fin M.k ↪ Fin 2`, restarted at `M`'s initial
state. The host's initial configuration is the embedding of `M`'s into the blank frame with
heads at `0` and empty prefix (`Turing.embedEmitCfg_eq`, field by field from the `Cfg.init`
equations; the selected bank is empty). By `Turing.embedEmitTM_runFrom` the host's run is the
embedding of `M`'s run, so the two have the same state and the same output at every time
(`Turing.embedEmitCfg_state`, `Turing.embedEmitCfg_output`). Hence they halt together with the
same output, and `t ≤ (t + 1)(log₂(t + 1) + 1)` pads the time. -/
private theorem tt_zero_tapes (M : FinTM Bool) (hk : M.k = 0) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨σ⟩ : Nonempty (Fin M.k ↪ Fin 2) := ⟨Fin.castLEEmb (by omega)⟩
  -- the host: R1 of `M.tm`, restarted at `M`'s initial state
  obtain ⟨N, hq, hr⟩ : ∃ N : MultiTapeTM 2 Bool M.State,
      (∀ x, N.initCfg x = Cfg.init M.tm.q₀ x) ∧
        ∀ (x : List Bool) (c : Cfg 2 Bool M.State x) (t : ℕ),
          N.runFrom c t = (embedEmitTM σ M.tm).runFrom c t :=
    ⟨_, fun x => MultiTapeTM.initCfg_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ x,
      fun _ c t => MultiTapeTM.runFrom_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ c t⟩
  -- the host's initial configuration is the embedding of `M`'s into the blank frame
  have hinit : ∀ x : List Bool,
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.initCfg x) =
        Cfg.init M.tm.q₀ x := by
    intro x
    rw [MultiTapeTM.initCfg_eq]
    refine embedEmitCfg_eq σ _ _ [] _ _ ?_ ?_ ?_ ?_ ?_
    · simp only [Cfg.init_state]
    · simp only [Cfg.init_inputPos]
    · simp only [Cfg.init_output, List.append_nil]
    · intro i
      exact (i.cast hk).elim0
    · intro j _
      exact ⟨funext fun p => by simp only [Cfg.init_workTapes],
        by simp only [Cfg.init_workTapePos]⟩
  -- the host's run is the embedding of `M`'s
  have hrun : ∀ (x : List Bool) (t : ℕ), N.runFrom (N.initCfg x) t =
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.runFrom (M.tm.initCfg x) t) := by
    intro x t
    rw [hq, ← hinit x, hr, embedEmitTM_runFrom]
  refine ⟨{ k := 2, State := M.State, tm := N }, 1, rfl, fun x o t h => ?_, fun x o h => ?_⟩
  · obtain ⟨hs, ho⟩ := (computesInTime_iff M x o t).1 h
    have hb : t ≤ 1 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := by
      rw [Nat.one_mul]
      exact le_mul_of_le_of_one_le (Nat.le_succ t) (by omega)
    refine ComputesInTime.mono ?_ hb
    rw [computesInTime_iff]
    show (N.runFrom (N.initCfg x) t).state = none ∧ (N.runFrom (N.initCfg x) t).output = o
    refine ⟨?_, ?_⟩
    · rw [hrun, embedEmitCfg_state, hs]
    · rw [hrun, embedEmitCfg_output, ho, List.nil_append]
  · obtain ⟨t, ht⟩ := h
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ x o t).1 ht
    have hs' : (N.runFrom (N.initCfg x) t).state = none := hs
    have ho' : (N.runFrom (N.initCfg x) t).output = o := ho
    rw [hrun, embedEmitCfg_state] at hs'
    rw [hrun, embedEmitCfg_output, List.nil_append] at ho'
    exact ⟨t, (computesInTime_iff M x o t).2 ⟨hs', ho'⟩⟩

/-- **The frame of the two-work-tape reduction** [HS66; AB09, §1.7, with Claim 1.5 for the
alphabet]: let `HS` be a machine over the zone alphabet `Turing.ZoneSym M.k` with two work tapes
that reproduces each halting run of `M` of `t` steps on the encoded input `x.map Sum.inl`, with
the encoded output, within `c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of
which on an encoded input is the encoding of an output of `M`. Then `M` has a binary equivalent
with two work tapes, with the same overhead up to a constant, and whose completed outputs are
outputs of `M`.

**Proof sketch.** Reduce `HS` to the binary alphabet by `Turing.FinTM.alphabet_reduction_run`
along `Sum.inl : Bool ↪ ZoneSym M.k`, which keeps the two work tapes and multiplies the time by a
constant `c₂`; the constant of the result is `c₂ · c₁`. Forward, `M`'s run gives `HS`'s within
`c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and the reduction's forward direction gives the binary
machine's. Conversely, a completed output `w` of the binary machine comes from a completed output
`o'` of `HS` on the encoded input such that every binary word encoding to `o'` is `w`; the
converse property of `HS` writes `o'` as the encoding of an output `v` of `M`, so `v = w`. -/
private theorem tt_frame (M : FinTM Bool) (HS : FinTM (ZoneSym M.k)) (hHS : HS.k = 2) (c₁ : ℕ)
    (hfwd : ∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
      HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
        (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1))))
    (hconv : ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
      HS.ComputesInTime (x.map Sum.inl) o' t' →
        ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨c₂, M', hk, hf, hc⟩ :=
    alphabet_reduction_run (Function.Embedding.inl : Bool ↪ ZoneSym M.k) HS
  have hinl : ⇑(Function.Embedding.inl : Bool ↪ ZoneSym M.k) = Sum.inl :=
    funext fun b => Function.Embedding.inl_apply b
  rw [hinl] at hf hc
  refine ⟨M', c₂ * c₁, hk.trans hHS, fun x o t h => ?_, fun x o h => ?_⟩
  · rw [Nat.mul_assoc]
    exact hf x o _ (hfwd x o t h)
  · obtain ⟨t', o', ht', hv⟩ := hc x o h
    obtain ⟨t, v, hM, rfl⟩ := hconv x o' t' ht'
    obtain rfl := hv v rfl
    exact ⟨t, hM⟩

/-- **The route of the two-work-tape reduction** [HS66; AB09, §1.7]: if every binary machine
with at least one work tape has a two-work-tape zone machine with the forward property and the
image converse of `tt_frame`, then every binary machine has a binary equivalent with two work
tapes, with overhead `O((t + 1) log(t + 1))` per run of `t` steps, whose completed outputs are
outputs of the source.

**Proof sketch.** Without work tapes, `tt_zero_tapes`; otherwise the hypothesis gives the zone
machine, and `tt_frame` finishes. -/
private theorem tt_route
    (hHS : ∀ M : FinTM Bool, 1 ≤ M.k →
      ∃ (HS : FinTM (ZoneSym M.k)) (_ : HS.k = 2) (c₁ : ℕ),
        (∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
          HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
            (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
        ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
          HS.ComputesInTime (x.map Sum.inl) o' t' →
            ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl)
    (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  by_cases hk : M.k = 0
  · exact tt_zero_tapes M hk
  · obtain ⟨HS, hHSk, c₁, hf, hc⟩ := hHS M (by omega)
    exact tt_frame M HS hHSk c₁ hf hc

/-! ### The leaf: one simulated transition on the home cell -/

/-- The states of the transition step of the two-work-tape simulation of `M` [HS66; AB09,
§1.7]: `Sum.inl q`, about to simulate one transition of `M` at state `q`, and `Sum.inr (q', m)`,
the transition done, with `M`'s successor state `q'` and the head moves `m` still pending. -/
private abbrev tt_LeafSt (M : FinTM Bool) : Type :=
  M.State ⊕ (M.State × (Fin M.k → SignType))

/-- The input symbol of the binary source read through the zone alphabet's embedding
`Sum.inl` (a cell that holds no binary symbol reads as blank). -/
private def tt_decodeIn {k : ℕ} : Option (ZoneSym k) → Option Bool
  | some (.inl b) => some b
  | _ => none

/-- The home tuple read from the home cell of the zoned tape (`Turing.zonedTape`): track `t`
reads the virtual symbol stored in its slot, a blank or unoccupied slot reading as blank. -/
private def tt_homeRead {k : ℕ} (w : Option (ZoneSym k)) (t : Fin k) : Option Bool :=
  (zoneCellOfCell w t).join

/-- The value track `t` holds after one transition of `M` with action `a` from the home
tuple `v`: the written symbol, or the old one when nothing is written. -/
private def tt_homeNew {k : ℕ} {S : Type} (a : Action k Bool S) (v : Fin k → Option Bool)
    (t : Fin k) : Option Bool :=
  (a.workTapes t).1.getD (v t)

/-- The head moves of one transition of `M` with action `a`. -/
private def tt_moves {k : ℕ} {S : Type} (a : Action k Bool S) (t : Fin k) : SignType :=
  (a.workTapes t).2

/-- **The transition step's table** [HS66; AB09, §1.7]. No public row applies a finite-state
transition to the home cell of the zoned tape and the input head in one step, so the
simulation writes this one leaf. At `Sum.inl q` it reads the home tuple from the home cell of
tape `0` (`tt_homeRead`) and the input symbol through `Sum.inl` (`tt_decodeIn`), applies `M`'s
transition at `q`, writes the new home tuple, moves the input head as `M` does, emits `M`'s
output symbol through `Sum.inl`, keeps both work heads, and goes to `Sum.inr (q', m)` with `M`'s
successor state and head moves, or halts when `M` halts. A state `Sum.inr _` halts (it is
redirected by the host and never runs). -/
private def tt_leafTr (M : FinTM Bool) (s : tt_LeafSt M) (inp : Option (ZoneSym M.k))
    (w : Fin 2 → Option (ZoneSym M.k)) : Action 2 (ZoneSym M.k) (tt_LeafSt M) :=
  match s with
  | .inl q =>
    { inputTape := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).inputTape
      workTapes := fun j => if j = 0 then
          (some (some (.inr fun t =>
            some (tt_homeNew (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0)))
              (tt_homeRead (w 0)) t))), 0)
        else (none, 0)
      output := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).output.map Sum.inl
      state := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).state.map fun q' =>
        .inr (q', tt_moves (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0)))) }
  | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transition step** [HS66; AB09, §1.7]: the two-tape machine over `Turing.ZoneSym M.k`
whose table is `tt_leafTr`. -/
private def tt_leafTM (M : FinTM Bool) : MultiTapeTM 2 (ZoneSym M.k) (tt_LeafSt M) where
  q₀ := .inl M.tm.q₀
  tr := tt_leafTr M

/-- The transition step keeps every work head. -/
private theorem tt_leafTM_tr_moves (M : FinTM Bool) (s : tt_LeafSt M) (inp : Option (ZoneSym M.k))
    (w : Fin 2 → Option (ZoneSym M.k)) (j : Fin 2) :
    (((tt_leafTM M).tr s inp w).workTapes j).2 = 0 := by
  rcases s with q | _
  · show (if j = 0 then _ else ((none : Option (Option (ZoneSym M.k))), (0 : SignType))).2 = 0
    split_ifs <;> rfl
  · rfl

/-- The transition step writes nothing on tape `1`. -/
private theorem tt_leafTM_tr_workTapes_of_ne (M : FinTM Bool) (q : M.State)
    (inp : Option (ZoneSym M.k)) (w : Fin 2 → Option (ZoneSym M.k)) {j : Fin 2} (hj : j ≠ 0) :
    ((tt_leafTM M).tr (.inl q) inp w).workTapes j = (none, 0) :=
  if_neg hj

/-- **One transition step** [HS66; AB09, §1.7]: from a configuration at `Sum.inl q`, one step
of the transition machine applies `M`'s transition `a` at `q` to the home tuple read from the
home cell and to the decoded input symbol. It writes the new home tuple into the cell under
head `0` and leaves tape `1`, moves the input head by `a`'s input move, keeps both work heads,
appends `a`'s output symbol through `Sum.inl`, and goes to `Sum.inr (q', m)` for `a`'s
successor `q'` and head moves `m`, or halts with `a`.

**Proof sketch.** `Turing.MultiTapeTM.step_of_some` applies the table's action; its fields are
read through `Turing.Action.apply_state`, `_inputPos`, `_workTapePos`, `_output` and
`Turing.Action.apply_workTapes`, the table being this file's own definition. -/
private theorem tt_leaf_step (M : FinTM Bool) {x : List (ZoneSym M.k)}
    (c : Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x) (q : M.State) (hc : c.state = some (.inl q)) :
    (tt_leafTM M).step c =
      { state := (M.tm.tr q (tt_decodeIn c.inputSymbol)
            (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).state.map fun q' =>
          .inr (q', tt_moves (M.tm.tr q (tt_decodeIn c.inputSymbol)
            (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))))
        inputPos := moveInputPos c.inputPos (M.tm.tr q (tt_decodeIn c.inputSymbol)
          (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).inputTape
        workTapes := fun j => if j = 0 then
            Function.update (c.workTapes 0) (c.workTapePos 0) (some (.inr fun t =>
              some (tt_homeNew (M.tm.tr q (tt_decodeIn c.inputSymbol)
                (tt_homeRead (c.workTapes 0 (c.workTapePos 0))))
                (tt_homeRead (c.workTapes 0 (c.workTapePos 0))) t)))
          else c.workTapes j
        workTapePos := c.workTapePos
        output := c.output ++ ((M.tm.tr q (tt_decodeIn c.inputSymbol)
          (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).output.map Sum.inl).toList } := by
  have hW : c.workTapeSymbols = fun i => c.workTapes i (c.workTapePos i) :=
    funext (Cfg.workTapeSymbols_eq c)
  rw [MultiTapeTM.step_of_some hc]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Action.apply_state, hW]
    rfl
  · rw [Action.apply_inputPos, hW]
    rfl
  · funext j p
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq, hW]
    by_cases hj : j = 0
    · subst hj
      rfl
    · rw [tt_leafTM_tr_workTapes_of_ne M q _ _ hj, Option.getD_none, Function.update_eq_self]
      show c.workTapes j p = (if j = 0 then _ else c.workTapes j) p
      rw [if_neg hj]
  · funext j
    rw [Action.apply_workTapePos, tt_leafTM_tr_moves, SignType.coe_zero, add_zero]
  · rw [Action.apply_output, hW]
    rfl

/-! ### The controller: the phase host over the transition step and the track steps -/

/-- **A track-step family** for `k` tracks with constant `A` [AB09, §1.7]: per direction `dir`
(`true` for a right move) and track `t`, a two-tape machine over `Turing.ZoneSym k` with finite
states, an entry, live exits, and per input a `Turing.Contract` with precondition
`Turing.zoneRowPre`, time at most `A · (2^{i₀} + 1)` for the scanned index `i₀`, and an endpoint
at the data `Turing.zoneTrackStepData dir t D` with the scratch head, the input head and the
output kept. `Turing.exists_zoneTrackStepTM` gives one. -/
private structure tt_Fam (k A : ℕ) where
  /-- the state types -/
  S : Bool → Fin k → Type
  /-- their finiteness -/
  fin : ∀ dir t, Fintype (S dir t)
  /-- their decidable equality -/
  dec : ∀ dir t, DecidableEq (S dir t)
  /-- the machines -/
  M : ∀ dir t, MultiTapeTM 2 (ZoneSym k) (S dir t)
  /-- the entries -/
  entry : ∀ dir t, S dir t
  /-- the exits -/
  X : ∀ dir t, Set (Option (S dir t))
  /-- the exits are live -/
  none_nmem : ∀ dir t, none ∉ X dir t
  /-- the contracts -/
  R : ∀ dir t (x : List (ZoneSym k)), Contract (M dir t) (entry dir t) (X dir t) (ZoneData k) x
  /-- their precondition -/
  pre : ∀ dir t x, (R dir t x).pre = zoneRowPre
  /-- their time and endpoint -/
  spec : ∀ dir t x (D : ZoneData k) (d : Cfg 2 (ZoneSym k) (S dir t) x),
    d.state = some (entry dir t) → zoneRowPre D d →
      (R dir t x).time D d ≤ A * (2 ^ zoneRebalanceIndex dir t D + 1) ∧
      zoneRowPre (zoneTrackStepData dir t D) ((R dir t x).post D d) ∧
      ((R dir t x).post D d).workTapePos 1 = d.workTapePos 1 ∧
      ((R dir t x).post D d).inputPos = d.inputPos ∧ ((R dir t x).post D d).output = d.output

/-- The direction of a head move: `true` for a right move, `false` otherwise. -/
private def tt_dir : SignType → Bool
  | .pos => true
  | _ => false

/-- The phase index of the simulation: `none` for the transition step, `some (q', m, t)` for
the step of track `t` in the round whose transition went to `q'` with head moves `m`. -/
private abbrev tt_I (M : FinTM Bool) : Type :=
  Option (M.State × (Fin M.k → SignType) × Fin M.k)

/-- The phases' state types: the transition step's, and per track the track step's of its
direction. -/
private def tt_Ph (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) : tt_I M → Type
  | none => tt_LeafSt M
  | some (_, m, t) => F.S (tt_dir (m t)) t

/-- The phases' machines: the transition step, and per track the track step of its
direction (for a stay, it is entered and left at once). -/
private def tt_Mf (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → MultiTapeTM 2 (ZoneSym M.k) (tt_Ph M F i)
  | none => tt_leafTM M
  | some (_, m, t) => F.M (tt_dir (m t)) t

/-- The state after the step of track `t`: the next track's entry, or the transition step at
`q'` after the last track. -/
private def tt_next (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (t : Fin M.k) : Σ i, tt_Ph M F i :=
  if h : t.val + 1 < M.k then
    ⟨some (q', m, ⟨t.val + 1, h⟩), F.entry (tt_dir (m ⟨t.val + 1, h⟩)) ⟨t.val + 1, h⟩⟩
  else ⟨none, .inl q'⟩

open Classical in
/-- **The redirects** of the simulation's phase host: the transition step's exit
`Sum.inr (q', m)` goes to track `0`'s entry; a track's exit (for a stay, its entry) goes to
`tt_next`; nothing else is redirected. -/
private noncomputable def tt_red (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k) :
    (i : tt_I M) → tt_Ph M F i → Option (Σ i, tt_Ph M F i)
  | none, .inl _ => none
  | none, .inr (q', m) => some ⟨some (q', m, ⟨0, hk⟩), F.entry (tt_dir (m ⟨0, hk⟩)) ⟨0, hk⟩⟩
  | some (q', m, t), s =>
    if (m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨ (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)
    then some (tt_next M F q' m t) else none

open Classical in
/-- A track's exit (for a stay, its entry) is redirected to `tt_next`. -/
private theorem tt_red_track_pos (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k) (s : F.S (tt_dir (m t)) t)
    (h : (m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨ (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)) :
    tt_red M F hk (some (q', m, t)) s = some (tt_next M F q' m t) :=
  if_pos h

open Classical in
/-- Every other state of a track's phase is not redirected. -/
private theorem tt_red_track_neg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k) (s : F.S (tt_dir (m t)) t)
    (h : ¬((m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨
      (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t))) :
    tt_red M F hk (some (q', m, t)) s = none :=
  if_neg h

/-- The phases' state types are finite. -/
private def tt_phFin (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → Fintype (tt_Ph M F i)
  | none => inferInstanceAs (Fintype (tt_LeafSt M))
  | some (_, m, t) => F.fin (tt_dir (m t)) t

/-- The phases' state types have decidable equality. -/
private def tt_phDec (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → DecidableEq (tt_Ph M F i)
  | none => inferInstanceAs (DecidableEq (tt_LeafSt M))
  | some (_, m, t) => F.dec (tt_dir (m t)) t

/-- **The two-work-tape zone machine** [HS66; AB09, §1.7]: the phase host
`Turing.phaseHostTM` over the transition step and the track steps of `F`, started at the
transition step at `M`'s initial state. Tape `0` is the zoned tape, tape `1` the scratch
tape. -/
private noncomputable def tt_HS (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k) :
    FinTM (ZoneSym M.k) :=
  letI := tt_phFin M F
  letI := tt_phDec M F
  { k := 2
    State := Σ i, tt_Ph M F i
    tm := phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) }

/-! ### The configurations at the round boundaries -/

/-- **A configuration at a phase boundary**: state `s`, input head at `ip`, output `out`, tape
`0` the zoned tape of `D` with its head at home, tape `1` blank with its head at `0`. -/
private def tt_cfg {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S) (D : ZoneData k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) : Cfg 2 (ZoneSym k) S x :=
  ⟨s, ip, fun j => if j = 0 then zonedTape D.2 else fun _ => none, fun _ => 0, out⟩

/-- Renaming the state of a phase-boundary configuration renames its state only. -/
private theorem tt_cfg_mapState {k : ℕ} {S S' : Type} {x : List (ZoneSym k)} (s : Option S)
    (D : ZoneData k) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) (f : S → S') :
    (tt_cfg s D ip out).mapState f = (tt_cfg (s.map f) D ip out : Cfg 2 (ZoneSym k) S' x) :=
  Cfg.mapState_eq_of_fields _ f _ rfl rfl rfl rfl rfl

/-- A phase-boundary configuration satisfies the zone rows' precondition. -/
private theorem tt_cfg_rowPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S)
    (D : ZoneData k) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) :
    zoneRowPre D (tt_cfg s D ip out : Cfg 2 (ZoneSym k) S x) :=
  (zoneRowPre_iff D _).mpr ⟨rfl, rfl, fun _ => rfl⟩

/-- **A row endpoint is a phase-boundary configuration**: a configuration that satisfies the
zone rows' precondition at `D`, with head `1` at `0`, input head `ip` and output `out`, is
`tt_cfg` at `D` once its state is renamed to the constant `s`, if it is live.

**Proof sketch.** Field by field (`Turing.Cfg.mapState_eq_of_fields`): the state is `some s`
since `d` is live; tape `0` and head `0` are the precondition's (`Turing.zoneRowPre_iff`), tape `1`
is blank by it, head `1` is `h1`, and the input head and the output are the hypotheses. -/
private theorem tt_mapState_eq_cfg {k : ℕ} {S S' : Type} {x : List (ZoneSym k)}
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (hp : zoneRowPre D d) (s : S')
    (hs : d.state.isSome) (h1 : d.workTapePos 1 = 0) (ip : Fin (x.length + 2))
    (hi : d.inputPos = ip) (out : List (ZoneSym k)) (ho : d.output = out) :
    d.mapState (fun _ => s) = tt_cfg (some s) D ip out := by
  obtain ⟨h0, hp0, hb⟩ := (zoneRowPre_iff D d).mp hp
  obtain ⟨s₀, hs₀⟩ := Option.isSome_iff_exists.mp hs
  refine Cfg.mapState_eq_of_fields d _ _ ?_ hi ?_ ?_ ho
  · rw [hs₀]
    rfl
  · funext j p
    by_cases hj : j = 0
    · subst hj
      rw [h0]
      rfl
    · obtain rfl := Fin.eq_one_of_ne_zero j hj
      rw [hb p]
      rfl
  · funext j
    by_cases hj : j = 0
    · subst hj
      rw [hp0]
      rfl
    · obtain rfl := Fin.eq_one_of_ne_zero j hj
      rw [h1]
      rfl

/-! ### One track's phase -/

/-- The data after track `t`'s step for head move `s`: unchanged for a stay, otherwise
`Turing.zoneTrackStepData` in the move's direction. -/
private def tt_trackData {k : ℕ} (s : SignType) (t : Fin k) (D : ZoneData k) : ZoneData k :=
  if s = 0 then D else zoneTrackStepData (tt_dir s) t D

/-- The scanned index of track `t`'s step for head move `s`: `0` for a stay. -/
private def tt_idx {k : ℕ} (s : SignType) (t : Fin k) (D : ZoneData k) : ℕ :=
  if s = 0 then 0 else zoneRebalanceIndex (tt_dir s) t D

/-- The time of track `t`'s phase before its dispatch step: `0` for a stay, otherwise the
track step's contract time from the phase-boundary configuration. -/
private def tt_trackTime (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (t : Fin M.k) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) : ℕ :=
  if m t = 0 then 0 else
    (F.R (tt_dir (m t)) t x).time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)

/-- The step of track `t` leaves its phase: `tt_next` is at another phase. -/
private theorem tt_next_ne (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (t : Fin M.k) : (tt_next M F q' m t).1 ≠ some (q', m, t) := by
  unfold tt_next
  split_ifs <;> simp [Fin.ext_iff]

/-- **A track's contract inside the host** [HS66; AB09, §1.7]: a contract for track `t`'s phase
from its entry, whose exits are live and are exactly the states that `tt_red` redirects, gives a
live run of the zone machine from the phase-boundary configuration at that entry, one dispatch
step past the contract's time, to the phase-boundary configuration at `tt_next` with data `D'`,
if the contract's endpoint satisfies the rows' precondition at `D'` and keeps head `1`, the input
head and the output.

**Proof sketch.** The redirect table meets the hypotheses of the phase host's contract form
`Turing.Contract.inPhase` (`tt_red_track_pos`, `tt_red_track_neg`), every target at another
phase (`tt_next_ne`). Its run (`Turing.Contract.inPhase_time`) and its liveness
(`Turing.Contract.live`) give the segment; its exit is the target `tt_next`, and its endpoint is
the contract's with that state (`Turing.Contract.inPhase_post`), the phase-boundary configuration
there (`tt_mapState_eq_cfg`). -/
private theorem tt_phase_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k)
    {X : Set (Option (tt_Ph M F (some (q', m, t))))}
    (C : Contract (tt_Mf M F (some (q', m, t))) (F.entry (tt_dir (m t)) t) X (ZoneData M.k) x)
    (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ ((m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨
      (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)))
    (D D' : ZoneData M.k) (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k))
    (hpre : C.pre D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out))
    (hpost : zoneRowPre D' (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)))
    (h1 : (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)).workTapePos 1 = 0)
    (hin : (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)).inputPos = ip)
    (hout : (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)).output = out) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True)
      (tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out)
      (tt_cfg (some (tt_next M F q' m t)) D' ip out)
      (C.time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out) + 1) := by
  set c : Cfg 2 (ZoneSym M.k) (tt_Ph M F (some (q', m, t))) x :=
    tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out
  set d : Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) x :=
    tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out
  have hdc : d.mapState (fun _ => F.entry (tt_dir (m t)) t) = c := tt_cfg_mapState _ _ _ _ _
  have hred : ∀ s, some s ∉ X → tt_red M F hk (some (q', m, t)) s = none :=
    fun s hs => tt_red_track_neg M F hk q' m t s fun h => hs ((hX s).mpr h)
  have hsome : ∀ s, some s ∈ X →
      ∃ q, tt_red M F hk (some (q', m, t)) s = some q ∧ q.1 ≠ some (q', m, t) :=
    fun s hs => ⟨_, tt_red_track_pos M F hk q' m t s ((hX s).mp hs), tt_next_ne M F q' m t⟩
  set C' := Contract.inPhase (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) (some (q', m, t))
    C hnone hred hsome with hC'
  have hs : d.state = some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩ := rfl
  have hp : C'.pre D d := by
    rw [hC', Contract.inPhase_pre, hdc]
    exact hpre
  have hT : C'.time D d = C.time D c + 1 := by
    rw [hC', Contract.inPhase_time, hdc]
  have hP : C'.post D d = (C.post D c).bindState (tt_red M F hk (some (q', m, t))) := by
    rw [hC', Contract.inPhase_post, hdc]
  obtain ⟨s, hsX, hst⟩ := C'.exit_mem D d hs hp
  rw [tt_red_track_pos M F hk q' m t s ((hX s).mp hsX), hP, Cfg.bindState_state] at hst
  obtain ⟨s', hs', -⟩ := Option.bind_eq_some_iff.mp hst
  have hE : C'.post D d = tt_cfg (some (tt_next M F q' m t)) D' ip out := by
    rw [← tt_mapState_eq_cfg D' (C.post D c) hpost (tt_next M F q' m t) (by rw [hs']; rfl) h1 ip
      hin out hout, hP]
    refine (Cfg.mapState_eq_of_fields _ _ _ ?_ (by rw [Cfg.bindState_inputPos])
      (by funext j p; rw [Cfg.bindState_workTapes]) (by funext j; rw [Cfg.bindState_workTapePos])
      (by rw [Cfg.bindState_output])).symm
    rw [Cfg.bindState_state, hst, hs']
    rfl
  refine (segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩
  · rw [← hT, ← hE]
    exact C'.run D d hs hp
  · rw [Set.mem_singleton_iff]
    exact C'.live D d hs hp (hT ▸ hu)

/-- **One track's phase** [HS66; AB09, §1.7]: from the entry of track `t`'s phase, at a
phase-boundary configuration with data `D`, the zone machine runs live for the phase's time
plus one dispatch step to the phase-boundary configuration at `tt_next` with the data after
track `t`'s step, the input head and the output kept; the phase's time is at most
`A · (2^{i₀} + 1)` for its scanned index `i₀`.

**Proof sketch.** By `tt_phase_seg`, with the zero-time contract (`Turing.Contract.zero`) for a
stay, whose only exit is the entry, and the track step's contract for a move, whose specification
gives the endpoint and the time bound. -/
private theorem tt_track_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k)
    (D : ZoneData M.k) (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True)
        (tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out)
        (tt_cfg (some (tt_next M F q' m t)) (tt_trackData (m t) t D) ip out)
        (tt_trackTime M F x m t D ip out + 1) ∧
      tt_trackTime M F x m t D ip out ≤ A * (2 ^ tt_idx (m t) t D + 1) := by
  by_cases h0 : m t = 0
  · -- a stay: the zero-time contract, redirected at once
    have hT : tt_trackTime M F x m t D ip out = 0 := if_pos h0
    have hD : tt_trackData (m t) t D = D := if_pos h0
    rw [hT, hD]
    refine ⟨?_, Nat.zero_le _⟩
    have H := tt_phase_seg M F hk q' m t
      (Contract.zero (tt_Mf M F (some (q', m, t))) (F.entry (tt_dir (m t)) t) (ZoneData M.k) x)
      (fun h => Option.noConfusion (Set.mem_singleton_iff.mp h))
      (fun s => ⟨fun h => Or.inl ⟨h0, Option.some.inj (Set.mem_singleton_iff.mp h)⟩,
        fun h => h.elim (fun h' => by rw [h'.2]; exact Set.mem_singleton _)
          (fun h' => absurd h0 h'.1)⟩)
      D D ip out (by rw [Contract.zero_pre]; trivial)
      (by rw [Contract.zero_post]; exact tt_cfg_rowPre _ D ip out)
      (by rw [Contract.zero_post]; rfl) (by rw [Contract.zero_post]; rfl)
      (by rw [Contract.zero_post]; rfl)
    rwa [Contract.zero_time] at H
  · -- a move: the track step's contract
    obtain ⟨htime, hpost, h1, hin, hout⟩ := F.spec (tt_dir (m t)) t x D
      (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out) rfl (tt_cfg_rowPre _ D ip out)
    have hT : tt_trackTime M F x m t D ip out =
        (F.R (tt_dir (m t)) t x).time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out) :=
      if_neg h0
    have hD : tt_trackData (m t) t D = zoneTrackStepData (tt_dir (m t)) t D := if_neg h0
    have hI : tt_idx (m t) t D = zoneRebalanceIndex (tt_dir (m t)) t D := if_neg h0
    rw [hT, hD, hI]
    refine ⟨tt_phase_seg M F hk q' m t (F.R (tt_dir (m t)) t x) (F.none_nmem _ _)
      (fun s => ⟨fun h => Or.inr ⟨h0, h⟩, fun h => h.elim (fun h' => absurd h'.1 h0) And.right⟩)
      D _ ip out (by rw [F.pre]; exact tt_cfg_rowPre _ D ip out) hpost h1 hin hout, htime⟩

/-! ### One round: the transition step, then every track -/

/-- **A round's start configuration** at the transition step: tape `0` is the zoned tape of `D`
except at the home cell, which holds `h0`; the rest as in `tt_cfg`. The first round starts with
a blank home cell, every later one with the zoned tape's own. -/
private def tt_cfg0 {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S) (D : ZoneData k)
    (h0 : Option (ZoneSym k)) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) :
    Cfg 2 (ZoneSym k) S x :=
  ⟨s, ip, fun j => if j = 0 then Function.update (zonedTape D.2) 0 h0 else fun _ => none,
    fun _ => 0, out⟩

/-- The transition of `M` at `q` on input symbol `inp` from the homes of `D`. -/
private def tt_act (M : FinTM Bool) (q : M.State) (inp : Option Bool) (D : ZoneData M.k) :
    Action M.k Bool M.State :=
  M.tm.tr q inp fun t => (D.2 t).home

/-- The data after the home write of action `a`. -/
private def tt_homeData {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) :
    ZoneData k :=
  ⟨D.1, fun t => zoneHomeWrite (D.2 t) (tt_homeNew a (fun t => (D.2 t).home) t)⟩

/-- The data after the steps of the tracks below `j`, for head moves `m`, from `D`. -/
private def tt_Dtr {k : ℕ} (m : Fin k → SignType) (D : ZoneData k) : ℕ → ZoneData k
  | 0 => D
  | j + 1 => if h : j < k then tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m D j) else tt_Dtr m D j

/-- The state at the start of track `j`'s phase, or the transition step at `q'` after the
last track. -/
private def tt_stAt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (j : ℕ) : Σ i, tt_Ph M F i :=
  if h : j < M.k then ⟨some (q', m, ⟨j, h⟩), F.entry (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩⟩
  else ⟨none, .inl q'⟩

/-- The time of track `j`'s phase in a round, with its dispatch step. -/
private def tt_τ (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (j : ℕ) : ℕ :=
  if h : j < M.k then tt_trackTime M F x m ⟨j, h⟩ (tt_Dtr m D j) ip out + 1 else 0

/-- Below the track count, a track's phase time in a round is its phase's time plus the dispatch
step. -/
private theorem tt_τ_of_lt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (j : ℕ) (hj : j < M.k) :
    tt_τ M F x m D ip out j = tt_trackTime M F x m ⟨j, hj⟩ (tt_Dtr m D j) ip out + 1 :=
  dif_pos hj

/-- **The tracks of a round** [HS66; AB09, §1.7]: from track `0`'s entry, the zone machine runs
live through every track's phase in order, to the transition step at `q'` with the data after
every track's step, in `∑ j < k` of the phases' times.

**Proof sketch.** `Turing.Segment.iterate_seq` over the tracks, each track by `tt_track_seg`;
consecutive boundaries match because `tt_next` at track `j` is `tt_stAt` at `j + 1`. -/
private theorem tt_tracks_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (D : ZoneData M.k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cfg (some (tt_stAt M F q' m 0)) D ip out)
      (tt_cfg (some ⟨none, .inl q'⟩) (tt_Dtr m D M.k) ip out)
      (∑ j ∈ Finset.range M.k, tt_τ M F x m D ip out j) := by
  have hend : tt_stAt M F q' m M.k = ⟨none, .inl q'⟩ := dif_neg (lt_irrefl _)
  have H := Segment.iterate_seq
    (M := phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) (F := {none})
    (P := fun _ => True)
    (fun j => (tt_cfg (some (tt_stAt M F q' m j)) (tt_Dtr m D j) ip out :
      Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) x))
    (tt_τ M F x m D ip out) trivial M.k (fun j hj => ?_)
  · dsimp only at H
    rw [hend] at H
    exact H
  · have hs : tt_stAt M F q' m j = ⟨some (q', m, ⟨j, hj⟩), F.entry (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩⟩ :=
      dif_pos hj
    have hn : tt_next M F q' m ⟨j, hj⟩ = tt_stAt M F q' m (j + 1) := rfl
    have hD : tt_Dtr m D (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) := dif_pos hj
    have hτ := tt_τ_of_lt M F x m D ip out j hj
    show Segment _ _ _ (tt_cfg (some (tt_stAt M F q' m j)) (tt_Dtr m D j) ip out)
      (tt_cfg (some (tt_stAt M F q' m (j + 1))) (tt_Dtr m D (j + 1)) ip out) _
    rw [hs, hD, hτ, ← hn]
    exact (tt_track_seg M F hk q' m ⟨j, hj⟩ (tt_Dtr m D j) ip out).1

/-- **One round** [HS66; AB09, §1.7]. From the transition step at `q`, with data `D` whose
homes are what the home cell `h0` reads and with decoded input symbol `inp`, let `a` be `M`'s
transition at `q` on `inp` and the homes of `D`. If `a` halts, the zone machine halts after one
step with `a`'s output symbol appended. Otherwise, with successor `q'`, it runs live to the
transition step at `q'`, with the data after the home write and every track's step, the input
head moved by `a` and `a`'s output symbol appended, in `2 + ∑ j < k` of the tracks' phase times.

**Proof sketch.** One transition step (`tt_leaf_step`) writes the home tuple: the home cell
becomes the zoned tape's of the written data (`Turing.zonedTape_homeWrite`). In the host it is
the tagged phase run (`Turing.phaseHostTM_run_le`, for a halt) or, with the redirect of its
exit, two steps to track `0`'s entry (`Turing.phaseHostTM_run`); the tracks follow
(`tt_tracks_seg`) and the two segments concatenate (`Turing.Segment.trans`). -/
private theorem tt_round (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q : M.State) (D : ZoneData M.k) (h0 : Option (ZoneSym M.k))
    (hread : ∀ t, tt_homeRead h0 t = (D.2 t).home) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (inp : Option Bool)
    (hinp : tt_decodeIn (tt_cfg0 (some (.inl q)) D h0 ip out :
      Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).inputSymbol = inp) :
    ((tt_act M q inp D).state = none →
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
          ((tt_cfg0 (some (.inl q)) D h0 ip out :
            Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none)) 1).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
          ((tt_cfg0 (some (.inl q)) D h0 ip out :
            Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none)) 1).output =
        out ++ ((tt_act M q inp D).output.map Sum.inl).toList) ∧
    ∀ q', (tt_act M q inp D).state = some q' →
      Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True)
        ((tt_cfg0 (some (.inl q)) D h0 ip out :
          Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none))
        (tt_cfg (some ⟨none, .inl q'⟩)
          (tt_Dtr (tt_moves (tt_act M q inp D)) (tt_homeData (tt_act M q inp D) D) M.k)
          (moveInputPos ip (tt_act M q inp D).inputTape)
          (out ++ ((tt_act M q inp D).output.map Sum.inl).toList))
        (2 + ∑ j ∈ Finset.range M.k, tt_τ M F x (tt_moves (tt_act M q inp D))
          (tt_homeData (tt_act M q inp D) D) (moveInputPos ip (tt_act M q inp D).inputTape)
          (out ++ ((tt_act M q inp D).output.map Sum.inl).toList) j) := by
  set c₀ : Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x := tt_cfg0 (some (.inl q)) D h0 ip out with hc₀
  set a := tt_act M q inp D with ha
  have hr : c₀.workTapes 0 (c₀.workTapePos 0) = h0 := by
    show Function.update (zonedTape D.2) 0 h0 0 = h0
    exact Function.update_self _ _ _
  have hR : tt_homeRead h0 = fun t => (D.2 t).home := funext hread
  have hstep := tt_leaf_step M c₀ q rfl
  rw [hr, hR, hinp] at hstep
  change (tt_leafTM M).step c₀ =
    { state := a.state.map fun q' => .inr (q', tt_moves a)
      inputPos := moveInputPos c₀.inputPos a.inputTape
      workTapes := fun j => if j = 0 then
          Function.update (c₀.workTapes 0) (c₀.workTapePos 0)
            (some (.inr fun t => some (tt_homeNew a (fun t => (D.2 t).home) t)))
        else c₀.workTapes j
      workTapePos := c₀.workTapePos
      output := c₀.output ++ (a.output.map Sum.inl).toList } at hstep
  have h₀ : (tt_Mf M F none).runFrom c₀ 0 = c₀ := MultiTapeTM.runFrom_zero
  have h1 : (tt_Mf M F none).runFrom c₀ 1 = (tt_leafTM M).step c₀ :=
    MultiTapeTM.runFrom_succ_eq_step.trans MultiTapeTM.runFrom_zero
  have hguard : ∀ u < 1, ∀ s, ((tt_Mf M F none).runFrom c₀ u).state = some s →
      tt_red M F hk none s = none := by
    intro u hu s hs
    rw [Nat.lt_one_iff.mp hu, h₀] at hs
    obtain rfl : (Sum.inl q : tt_LeafSt M) = s := Option.some.inj hs
    rfl
  refine ⟨fun hn => ?_, fun q' hq' => ?_⟩
  · have H := phaseHostTM_run_le (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) none c₀ 1
      hguard 1 le_rfl
    rw [H, h1, hstep]
    refine ⟨?_, ?_⟩
    · rw [Cfg.mapState_state]
      show Option.map _ (a.state.map _) = none
      rw [hn]
      rfl
    · rw [Cfg.mapState_output]
      rfl
  · have hs₁ : ((tt_leafTM M).step c₀).state = some (.inr (q', tt_moves a)) := by
      rw [hstep]
      show a.state.map _ = _
      rw [hq']
      rfl
    have hred : tt_red M F hk none (.inr (q', tt_moves a)) =
        some (tt_stAt M F q' (tt_moves a) 0) := by
      show some _ = some _
      rw [show tt_stAt M F q' (tt_moves a) 0 = _ from dif_pos hk]
    have H := phaseHostTM_run (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) none c₀ _ 1 h1
      _ hs₁ _ hred hguard
    have hend : ((tt_leafTM M).step c₀).mapState (fun _ => tt_stAt M F q' (tt_moves a) 0) =
        tt_cfg (some (tt_stAt M F q' (tt_moves a) 0)) (tt_homeData a D)
          (moveInputPos ip a.inputTape) (out ++ (a.output.map Sum.inl).toList) := by
      refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
      · rw [hs₁]
        rfl
      · rw [hstep]
        rfl
      · rw [hstep]
        funext j p
        by_cases hj : j = 0
        · subst hj
          show Function.update (Function.update (zonedTape D.2) 0 h0) 0 _ p = zonedTape _ p
          rw [Function.update_idem, zonedTape_homeWrite]
          rfl
        · show (if j = 0 then _ else c₀.workTapes j) p = (if j = 0 then _ else fun _ => none) p
          rw [if_neg hj, if_neg hj]
          show (if j = 0 then _ else fun _ => none) p = none
          rw [if_neg hj]
      · rw [hstep]
        rfl
      · rw [hstep]
        rfl
    have hlead : Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True) (c₀.mapState (Sigma.mk none))
        (tt_cfg (some (tt_stAt M F q' (tt_moves a) 0)) (tt_homeData a D)
          (moveInputPos ip a.inputTape) (out ++ (a.output.map Sum.inl).toList)) 2 := by
      refine (segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩
      · exact H.2.trans hend
      · rw [H.1 u (by omega), Set.mem_singleton_iff, Cfg.mapState_state]
        rcases Nat.lt_or_ge u 1 with h | h
        · rw [Nat.lt_one_iff.mp h, h₀]
          exact fun h => by cases h
        · obtain rfl : u = 1 := by omega
          rw [h1, hs₁]
          exact fun h => by cases h
    exact hlead.trans (tt_tracks_seg M F hk q' (tt_moves a) (tt_homeData a D) _ _)

/-- **The time bound of a round's track phases** [AB09, §1.7]: track `j`'s phase, with its
dispatch, takes at most `A · (2^{i₀} + 1) + 1` steps for its scanned index `i₀` (`0` for a
stay). -/
private theorem tt_τ_le (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List (ZoneSym M.k)) (m : Fin M.k → SignType) (D : ZoneData M.k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) (j : ℕ) (hj : j < M.k) :
    tt_τ M F x m D ip out j ≤ A * (2 ^ tt_idx (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) + 1) + 1 := by
  rw [tt_τ_of_lt M F x m D ip out j hj, Nat.add_le_add_iff_right]
  exact (tt_track_seg M F hk (x := x) M.tm.q₀ m ⟨j, hj⟩ (tt_Dtr m D j) ip out).2

/-! ### Fullness: the classical zone discipline -/

/-- **Fullness** of one track's contents [AB09, §1.7]: at every laid-out level `i` the two zones
together hold exactly `zoneCapacity i = 2 · 2^i` cells, and the right one holds `0`, `2^i` or
`2 · 2^i` (so the left one holds the complement: each side is empty, half full or full). -/
private def tt_full {ℓ : ℕ} (z : ZoneContents ℓ) : Prop :=
  ∀ i : Fin ℓ, (z.left i).length + (z.right i).length = zoneCapacity i.val ∧
    ((z.right i).length = 0 ∨ (z.right i).length = 2 ^ i.val ∨
      (z.right i).length = zoneCapacity i.val)

/-- The empty contents at level `0` are full (there is no level). -/
private theorem tt_full_empty : tt_full (ZoneContents.empty 0) :=
  fun i => i.elim0

/-- The home write keeps fullness: it changes no zone. -/
private theorem tt_full_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool)
    (hz : tt_full z) : tt_full (zoneHomeWrite z v) := by
  intro i
  rw [zoneHomeWrite_left, zoneHomeWrite_right]
  exact hz i

/-- **The extension keeps fullness**: the old levels are kept and the new one is half full on
both sides (`Turing.ZoneContents.extend_words_castSucc`, `_last`). -/
private theorem tt_full_extend {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z) :
    tt_full z.extend := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hl := ZoneContents.extend_words_last false z
    have hr := ZoneContents.extend_words_last true z
    rw [ZoneContents.words_false] at hl
    rw [ZoneContents.words_true] at hr
    rw [hl, hr, List.length_replicate, Fin.val_last, zoneCapacity_eq]
    exact ⟨by ring, Or.inr (Or.inl rfl)⟩
  · have hl := ZoneContents.extend_words_castSucc false z i
    have hr := ZoneContents.extend_words_castSucc true z i
    rw [ZoneContents.words_false, ZoneContents.words_false] at hl
    rw [ZoneContents.words_true, ZoneContents.words_true] at hr
    rw [hl, hr, Fin.coe_castSucc]
    exact hz i

/-- **Fullness gives the classical state of a right move** [AB09, §1.7]: below the scanned
index `j` the right zones are empty and the left ones full, the right zone `j` holds at least
`2^j` cells, and the left zone `j` has room for `2^j` cells (the hypotheses of
`Turing.zoneCascadeRight_lengths`).

**Proof sketch.** The right zones below `j` are empty (`Turing.zoneShiftIndex_empty`), so by
fullness the left ones hold the whole capacity; the right zone `j` is nonempty
(`Turing.zoneShiftIndex_nonempty`), so by fullness it holds `2^j` or `2 · 2^j` cells, and the
left zone `j` the rest of the capacity `2 · 2^j`. -/
private theorem tt_full_pre_true {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z) {j : ℕ}
    (hj : zoneShiftIndex true z = j) (h : j < ℓ) :
    (∀ k (hk : k < j), z.right ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j), (z.left ⟨k, by omega⟩).length = zoneCapacity k) ∧
    2 ^ j ≤ (z.right ⟨j, h⟩).length ∧ (z.left ⟨j, h⟩).length + 2 ^ j ≤ zoneCapacity j := by
  subst hj
  have hr (k : ℕ) (hk : k < zoneShiftIndex true z) : z.right ⟨k, by omega⟩ = [] := by
    have := zoneShiftIndex_empty true z ⟨k, by omega⟩ hk
    rwa [ZoneContents.words_true] at this
  have hne := zoneShiftIndex_nonempty true z h
  rw [ZoneContents.words_true] at hne
  have hpos : 0 < (z.right ⟨_, h⟩).length := List.length_pos_iff.mpr hne
  obtain ⟨hsum, hcase⟩ := hz ⟨_, h⟩
  have hc := zoneCapacity_eq (zoneShiftIndex true z)
  have hsum' : (z.left ⟨_, h⟩).length + (z.right ⟨_, h⟩).length =
      zoneCapacity (zoneShiftIndex true z) := hsum
  have hcase' : (z.right ⟨_, h⟩).length = 0 ∨
      (z.right ⟨_, h⟩).length = 2 ^ zoneShiftIndex true z ∨
      (z.right ⟨_, h⟩).length = zoneCapacity (zoneShiftIndex true z) := hcase
  have hdonor : 2 ^ zoneShiftIndex true z ≤ (z.right ⟨_, h⟩).length := by
    rcases hcase' with h0 | h0 | h0 <;> omega
  refine ⟨hr, fun k hk => ?_, hdonor, by omega⟩
  have := (hz ⟨k, by omega⟩).1
  rwa [hr k hk, List.length_nil, add_zero] at this

/-- **Fullness gives the classical state of a left move**: the mirror of `tt_full_pre_true`, the
hypotheses of `Turing.zoneCascadeLeft_lengths`.

**Proof sketch.** As for `tt_full_pre_true`, with the left stack feeding: the left zones below
the index are empty, so the right ones are full, and the left donor holds at least `2^j` cells,
so the right zone at the index has room for `2^j`. -/
private theorem tt_full_pre_false {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z) {j : ℕ}
    (hj : zoneShiftIndex false z = j) (h : j < ℓ) :
    (∀ k (hk : k < j), z.left ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j), (z.right ⟨k, by omega⟩).length = zoneCapacity k) ∧
    2 ^ j ≤ (z.left ⟨j, h⟩).length ∧ (z.right ⟨j, h⟩).length + 2 ^ j ≤ zoneCapacity j := by
  subst hj
  have hl (k : ℕ) (hk : k < zoneShiftIndex false z) : z.left ⟨k, by omega⟩ = [] := by
    have := zoneShiftIndex_empty false z ⟨k, by omega⟩ hk
    rwa [ZoneContents.words_false] at this
  have hne := zoneShiftIndex_nonempty false z h
  rw [ZoneContents.words_false] at hne
  have hpos : 0 < (z.left ⟨_, h⟩).length := List.length_pos_iff.mpr hne
  obtain ⟨hsum, hcase⟩ := hz ⟨_, h⟩
  have hc := zoneCapacity_eq (zoneShiftIndex false z)
  have hsum' : (z.left ⟨_, h⟩).length + (z.right ⟨_, h⟩).length =
      zoneCapacity (zoneShiftIndex false z) := hsum
  have hcase' : (z.right ⟨_, h⟩).length = 0 ∨
      (z.right ⟨_, h⟩).length = 2 ^ zoneShiftIndex false z ∨
      (z.right ⟨_, h⟩).length = zoneCapacity (zoneShiftIndex false z) := hcase
  have hdonor : 2 ^ zoneShiftIndex false z ≤ (z.left ⟨_, h⟩).length := by
    rcases hcase' with h0 | h0 | h0 <;> omega
  refine ⟨hl, fun k hk => ?_, hdonor, by omega⟩
  have := (hz ⟨k, by omega⟩).1
  rwa [hl k hk, List.length_nil, zero_add] at this

/-- **A right rebalance keeps fullness, and halves the levels below its index** [AB09, §1.7]:
under fullness, with a nonempty feeding zone at the scanned index `j`, the rebalanced contents
are full, every level below `j` is half full on both sides, and the levels above `j` are kept.

**Proof sketch.** Fullness and the scan give the classical pre-state of
`Turing.zoneCascadeRight_lengths` (`tt_full_pre_true`): right zones below `j` empty, left ones
full, a right donor of `2^j` or `2 · 2^j` cells and room for `2^j` on the left at `j`. The
cascade's lengths are then `2^k` on both sides below `j`, and at `j` the right side loses `2^j`
cells to the left; above `j` nothing changes (`Turing.zoneRebalance_frame`). -/
private theorem tt_full_rebalance_true {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex true z < ℓ) :
    tt_full (zoneRebalance true z) ∧
      ∀ i : Fin ℓ, i.val < zoneShiftIndex true z →
        ((zoneRebalance true z).left i).length = 2 ^ i.val ∧
          ((zoneRebalance true z).right i).length = 2 ^ i.val := by
  set j := zoneShiftIndex true z with hj
  obtain ⟨hr, hl, hdonor, hroom⟩ := tt_full_pre_true z hz hj.symm h
  obtain ⟨hsum, hcase⟩ := hz ⟨j, h⟩
  have hc : zoneCapacity j = 2 * 2 ^ j := zoneCapacity_eq j
  have hsum' : (z.left ⟨j, h⟩).length + (z.right ⟨j, h⟩).length = zoneCapacity j := hsum
  have hcase' : (z.right ⟨j, h⟩).length = 0 ∨ (z.right ⟨j, h⟩).length = 2 ^ j ∨
      (z.right ⟨j, h⟩).length = zoneCapacity j := hcase
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame true z k hk
  rw [zoneRebalance_of_lt true z h, zoneCascade_true] at hframe ⊢
  obtain ⟨hlow, hjr, hjl⟩ := zoneCascadeRight_lengths j h z hr hl hdonor hroom
  refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ hij => ?_⟩
  · rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨h1, h2⟩ := hlow i hij
      refine ⟨?_, Or.inr (Or.inl h1)⟩
      rw [h1, h2, zoneCapacity_eq]
      ring
    · refine ⟨?_, ?_⟩
      · show ((zoneCascadeRight _ z).left ⟨_, h⟩).length +
          ((zoneCascadeRight _ z).right ⟨_, h⟩).length = zoneCapacity _
        rw [hjr, hjl]
        omega
      · show ((zoneCascadeRight _ z).right ⟨_, h⟩).length = 0 ∨
          ((zoneCascadeRight _ z).right ⟨_, h⟩).length = 2 ^ _ ∨
          ((zoneCascadeRight _ z).right ⟨_, h⟩).length = zoneCapacity _
        rw [hjr]
        rcases hcase' with h0 | h0 | h0
        · omega
        · left
          show (z.right ⟨j, h⟩).length - 2 ^ j = 0
          omega
        · right; left
          show (z.right ⟨j, h⟩).length - 2 ^ j = 2 ^ j
          have : (z.right ⟨j, h⟩).length = 2 * 2 ^ j := h0.trans hc
          omega
    · obtain ⟨hfl, hfr⟩ := hframe ⟨i, hi⟩ hij
      rw [hfl, hfr]
      exact hz ⟨i, hi⟩
  · obtain ⟨h1, h2⟩ := hlow i hij
    exact ⟨h2, h1⟩

/-- **A left rebalance keeps fullness, and halves the levels below its index**: the mirror of
`tt_full_rebalance_true`.

**Proof sketch.** As for `tt_full_rebalance_true`, with the left stack feeding:
`Turing.zoneCascadeLeft_lengths` under the mirrored classical pre-state (`tt_full_pre_false`:
left zones below the index empty, so right ones full; the left donor holds `2^j` or `2 · 2^j`
cells), and `Turing.zoneRebalance_frame` above the index. -/
private theorem tt_full_rebalance_false {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex false z < ℓ) :
    tt_full (zoneRebalance false z) ∧
      ∀ i : Fin ℓ, i.val < zoneShiftIndex false z →
        ((zoneRebalance false z).left i).length = 2 ^ i.val ∧
          ((zoneRebalance false z).right i).length = 2 ^ i.val := by
  set j := zoneShiftIndex false z with hj
  obtain ⟨hl, hr, hdonor, hroom⟩ := tt_full_pre_false z hz hj.symm h
  obtain ⟨hsum, hcase⟩ := hz ⟨j, h⟩
  have hc : zoneCapacity j = 2 * 2 ^ j := zoneCapacity_eq j
  have hsum' : (z.left ⟨j, h⟩).length + (z.right ⟨j, h⟩).length = zoneCapacity j := hsum
  have hcase' : (z.right ⟨j, h⟩).length = 0 ∨ (z.right ⟨j, h⟩).length = 2 ^ j ∨
      (z.right ⟨j, h⟩).length = zoneCapacity j := hcase
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame false z k hk
  rw [zoneRebalance_of_lt false z h, zoneCascade_false] at hframe ⊢
  obtain ⟨hlow, hjl, hjr⟩ := zoneCascadeLeft_lengths j h z hl hr hdonor hroom
  refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ hij => hlow i hij⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · obtain ⟨h1, h2⟩ := hlow i hij
    refine ⟨?_, Or.inr (Or.inl h2)⟩
    rw [h1, h2, zoneCapacity_eq]
    ring
  · refine ⟨?_, ?_⟩
    · show ((zoneCascadeLeft _ z).left ⟨_, h⟩).length +
        ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = zoneCapacity _
      rw [hjr, hjl]
      omega
    · show ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = 0 ∨
        ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = 2 ^ _ ∨
        ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = zoneCapacity _
      rw [hjr]
      rcases hcase' with h0 | h0 | h0
      · right; left
        show (z.right ⟨j, h⟩).length + 2 ^ j = 2 ^ j
        omega
      · right; right
        show (z.right ⟨j, h⟩).length + 2 ^ j = zoneCapacity j
        omega
      · omega
  · obtain ⟨hfl, hfr⟩ := hframe ⟨i, hi⟩ hij
    rw [hfl, hfr]
    exact hz ⟨i, hi⟩

/-- The signed displacement of a head move in direction `dir`. -/
private def tt_shift : Bool → ℤ
  | true => 1
  | false => -1

/-- **A rebalance moves the represented tape** under fullness [AB09, §1.7]: the tape the
rebalanced track represents is the old one read one cell further in the move's direction. -/
private theorem tt_tape_rebalance {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex dir z < ℓ) (p : ℤ) :
    zoneTrackTape (zoneRebalance dir z) p = zoneTrackTape z (p + tt_shift dir) := by
  have hpow : ∀ j : ℕ, 2 ^ (j - 1) ≤ 2 ^ j := fun j => Nat.pow_le_pow_right (by norm_num) (by omega)
  cases dir
  · obtain ⟨-, hr, -, hroom⟩ := tt_full_pre_false z hz rfl h
    rw [zoneTrackTape_rebalance_left z h hr (le_trans (Nat.add_le_add_left (hpow _) _) hroom)]
    rfl
  · obtain ⟨-, hl, -, hroom⟩ := tt_full_pre_true z hz rfl h
    rw [zoneTrackTape_rebalance_right z h hl (le_trans (Nat.add_le_add_left (hpow _) _) hroom)]
    rfl

/-- **Fullness of the data**: every track's contents are full (`tt_full`). -/
private def tt_fullD {k : ℕ} (D : ZoneData k) : Prop :=
  ∀ t, tt_full (D.2 t)

/-- **One track's step keeps the data full and moves that track's represented tape**
[HS66; AB09, §1.7]: under fullness, after `Turing.zoneTrackStepData dir t D` the data are full,
track `t` represents its old tape read one cell further in direction `dir`, and every other
track represents its old tape.

**Proof sketch.** With a nonempty feeding zone the step is the rebalance of track `t`
(`Turing.zoneTrackStepData_of_lt`, `Turing.zoneRebalanceData_eq`): `tt_full_rebalance_true`/
`_false` and `tt_tape_rebalance` on track `t`, `Function.update_of_ne` elsewhere. Otherwise it
extends every track and then rebalances (`Turing.zoneTrackStepData_of_not_lt`,
`Turing.zoneExtendData_eq`): the extension keeps fullness (`tt_full_extend`) and every
represented tape (`Turing.zoneTrackTape_extend`), and the retried scan is below the new level
count (`Turing.zoneRebalanceIndex_extend_of_short`). -/
private theorem tt_trackStep_inv {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k)
    (hD : tt_fullD D) :
    tt_fullD (zoneTrackStepData dir t D) ∧
      ∀ t' p, zoneTrackTape ((zoneTrackStepData dir t D).2 t') p =
        zoneTrackTape (D.2 t') (if t' = t then p + tt_shift dir else p) := by
  have hreb : ∀ (E : ZoneData k), tt_fullD E → zoneRebalanceIndex dir t E < E.1 →
      tt_fullD (zoneRebalanceData dir t E) ∧
        ∀ t' p, zoneTrackTape ((zoneRebalanceData dir t E).2 t') p =
          zoneTrackTape (E.2 t') (if t' = t then p + tt_shift dir else p) := by
    intro E hE hlt
    rw [zoneRebalanceIndex_eq] at hlt
    rw [zoneRebalanceData_eq]
    refine ⟨fun t' => ?_, fun t' p => ?_⟩
    · show tt_full (Function.update E.2 t (zoneRebalance dir (E.2 t)) t')
      by_cases ht : t' = t
      · subst ht
        rw [Function.update_self]
        cases dir
        · exact (tt_full_rebalance_false _ (hE _) hlt).1
        · exact (tt_full_rebalance_true _ (hE _) hlt).1
      · rw [Function.update_of_ne ht]
        exact hE t'
    · show zoneTrackTape (Function.update E.2 t (zoneRebalance dir (E.2 t)) t') p = _
      by_cases ht : t' = t
      · subst ht
        rw [Function.update_self, if_pos rfl]
        exact tt_tape_rebalance dir _ (hE _) hlt p
      · rw [Function.update_of_ne ht, if_neg ht]
  by_cases hlt : zoneRebalanceIndex dir t D < D.1
  · rw [zoneTrackStepData_of_lt dir t hlt]
    exact hreb D hD hlt
  · rw [zoneTrackStepData_of_not_lt dir t hlt]
    have hidx := zoneRebalanceIndex_extend_of_short dir t D hlt
    have hE : tt_fullD (zoneExtendData D) := by
      rw [zoneExtendData_eq]
      exact fun t' => tt_full_extend _ (hD t')
    have hlt' : zoneRebalanceIndex dir t (zoneExtendData D) < (zoneExtendData D).1 := by
      rw [hidx, zoneExtendData_eq]
      exact Nat.lt_succ_self _
    obtain ⟨hf, htape⟩ := hreb _ hE hlt'
    refine ⟨hf, fun t' p => ?_⟩
    rw [htape]
    rw [zoneExtendData_eq]
    exact congrFun (zoneTrackTape_extend _) _

/-! ### The invariant: the represented tapes -/

/-- A nonzero head move's direction has the move's displacement. -/
private theorem tt_shift_dir (s : SignType) (hs : s ≠ 0) : tt_shift (tt_dir s) = (s : ℤ) := by
  cases s
  · exact absurd rfl hs
  · rfl
  · rfl

/-- **The tracks of a round keep fullness and move the represented tapes** [HS66; AB09,
§1.7]: after the steps of the tracks below `j` with head moves `m`, the data are full and every
track `t` below `j` represents its old tape shifted by `m t`, every other track its old tape.

**Proof sketch.** Induction on `j`, over the tracks of one round: a stay changes nothing, and a
move is `tt_trackStep_inv` with `tt_shift_dir`. -/
private theorem tt_Dtr_inv {k : ℕ} (m : Fin k → SignType) (D : ZoneData k) (hD : tt_fullD D)
    (j : ℕ) :
    tt_fullD (tt_Dtr m D j) ∧ ∀ t p, zoneTrackTape ((tt_Dtr m D j).2 t) p =
      zoneTrackTape (D.2 t) (if t.val < j then p + (m t : ℤ) else p) := by
  induction j with
  | zero =>
    exact ⟨hD, fun t p => by rw [if_neg (Nat.not_lt_zero _)]; rfl⟩
  | succ j ih =>
    obtain ⟨hf, htape⟩ := ih
    by_cases hj : j < k
    · have hDj : tt_Dtr m D (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) := dif_pos hj
      rw [hDj]
      by_cases h0 : m ⟨j, hj⟩ = 0
      · rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) = tt_Dtr m D j from if_pos h0]
        refine ⟨hf, fun t p => ?_⟩
        rw [htape]
        by_cases ht : t = ⟨j, hj⟩
        · subst ht
          rw [if_neg (lt_irrefl j), if_pos (Nat.lt_succ_self j), h0, SignType.coe_zero, add_zero]
        · have : t.val ≠ j := Fin.val_ne_of_ne ht
          by_cases htj : t.val < j
          · rw [if_pos htj, if_pos (by omega)]
          · rw [if_neg htj, if_neg (by omega)]
      · rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) =
          zoneTrackStepData (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩ (tt_Dtr m D j) from if_neg h0]
        obtain ⟨hf', htape'⟩ := tt_trackStep_inv (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩ _ hf
        refine ⟨hf', fun t p => ?_⟩
        rw [htape', htape]
        by_cases ht : t = ⟨j, hj⟩
        · subst ht
          rw [if_pos rfl, if_neg (lt_irrefl j), if_pos (Nat.lt_succ_self j),
            tt_shift_dir _ h0]
        · have : t.val ≠ j := Fin.val_ne_of_ne ht
          rw [if_neg ht]
          by_cases htj : t.val < j
          · rw [if_pos htj, if_pos (by omega)]
          · rw [if_neg htj, if_neg (by omega)]
    · have hDj : tt_Dtr m D (j + 1) = tt_Dtr m D j := dif_neg hj
      rw [hDj]
      refine ⟨hf, fun t p => ?_⟩
      rw [htape, if_pos (by omega), if_pos (by omega)]

/-- **The home write keeps fullness and writes the represented tapes at the head** [AB09,
§1.7]: after `tt_homeData a D`, track `t` represents its old tape with the new home value at
position `0`. -/
private theorem tt_homeData_inv {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k)
    (hD : tt_fullD D) :
    tt_fullD (tt_homeData a D) ∧ ∀ t p, zoneTrackTape ((tt_homeData a D).2 t) p =
      if p = 0 then tt_homeNew a (fun t => (D.2 t).home) t else zoneTrackTape (D.2 t) p :=
  ⟨fun t => tt_full_homeWrite _ _ (hD t), fun _ p => zoneTrackTape_homeWrite _ _ p⟩

/-- The data after a whole round, from `D`, for `M`'s action `a`. -/
private def tt_roundData {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) :
    ZoneData k :=
  tt_Dtr (tt_moves a) (tt_homeData a D) k

/-- **The represented tapes** of data `D` are the work tapes of `M`'s configuration `c`, read
relative to the heads. -/
private def tt_rep {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (D : ZoneData k) :
    Prop :=
  ∀ t p, zoneTrackTape (D.2 t) p = c.workTapes t (c.workTapePos t + p)

/-- Under the represented-tape invariant, the homes are the symbols under `M`'s heads. -/
private theorem tt_rep_home {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x)
    (D : ZoneData k) (h : tt_rep c D) : (fun t => (D.2 t).home) = c.workTapeSymbols := by
  funext t
  rw [Cfg.workTapeSymbols_eq, ← zoneTrackTape_zero, h t 0, add_zero]

/-- **One round preserves the invariant** [HS66; AB09, §1.7]: if `D` is full and represents
the work tapes of `M`'s live configuration `c` at `q`, then the round's data represent the work
tapes of `M`'s next configuration and are full. The action the round computes from the homes is
`M`'s own.

**Proof sketch.** The homes are the symbols under the heads (`tt_rep_home`), so the round's
action is `M`'s (`Turing.MultiTapeTM.step_of_some`). The home write puts the written symbol at
position `0` (`tt_homeData_inv`) and the tracks shift each represented tape by its head's
move (`tt_Dtr_inv`); `M`'s step writes at its head and then moves it
(`Turing.Action.apply_workTapes`, `Turing.Action.apply_workTapePos`), which is the same tape read
from the moved head. -/
private theorem tt_round_inv (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : M.State) (hq : c.state = some q) (D : ZoneData M.k) (hD : tt_fullD D)
    (hrep : tt_rep c D) :
    tt_act M q c.inputSymbol D = M.tm.tr q c.inputSymbol c.workTapeSymbols ∧
      tt_fullD (tt_roundData (tt_act M q c.inputSymbol D) D) ∧
      tt_rep (M.tm.step c) (tt_roundData (tt_act M q c.inputSymbol D) D) := by
  have hact : tt_act M q c.inputSymbol D = M.tm.tr q c.inputSymbol c.workTapeSymbols := by
    show M.tm.tr q c.inputSymbol (fun t => (D.2 t).home) = _
    rw [tt_rep_home c D hrep]
  set a := tt_act M q c.inputSymbol D with ha
  obtain ⟨hf₁, htape₁⟩ := tt_homeData_inv a D hD
  obtain ⟨hf₂, htape₂⟩ := tt_Dtr_inv (tt_moves a) (tt_homeData a D) hf₁ M.k
  refine ⟨hact, hf₂, fun t p => ?_⟩
  show zoneTrackTape ((tt_Dtr (tt_moves a) (tt_homeData a D) M.k).2 t) p = _
  rw [htape₂, if_pos t.isLt, htape₁, MultiTapeTM.step_of_some hq, Action.apply_workTapes,
    Action.apply_workTapePos, ← hact, ← tt_rep_home c D hrep]
  rw [show (a.workTapes t).1.getD ((fun t => (D.2 t).home) t) =
      tt_homeNew a (fun t => (D.2 t).home) t from rfl,
    show (a.workTapes t).2 = tt_moves a t from rfl]
  by_cases hp : p + (tt_moves a t : ℤ) = 0
  · rw [if_pos hp, show c.workTapePos t + (tt_moves a t : ℤ) + p = c.workTapePos t by omega,
      Function.update_self]
  · rw [if_neg hp, Function.update_of_ne (by omega), hrep t]
    congr 1
    ring

/-! ### The data orbit -/

/-- `M`'s run on `x`: its configuration after `r` steps. -/
private def tt_c (M : FinTM Bool) (x : List Bool) (r : ℕ) : Cfg M.k Bool M.State x :=
  M.tm.runFrom (M.tm.initCfg x) r

/-- **The data orbit** of the simulation of `M` on `x` [HS66; AB09, §1.7]: no level and empty
tracks at first; after each live step of `M`, the data after the round that simulates it. -/
private def tt_D (M : FinTM Bool) (x : List Bool) : ℕ → ZoneData M.k
  | 0 => ⟨0, fun _ => ZoneContents.empty 0⟩
  | r + 1 =>
    match (tt_c M x r).state with
    | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
    | none => tt_D M x r

/-- The orbit's step at a live configuration. -/
private theorem tt_D_succ (M : FinTM Bool) (x : List Bool) (r : ℕ) (q : M.State)
    (hq : (tt_c M x r).state = some q) :
    tt_D M x (r + 1) = tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r))
      (tt_D M x r) := by
  show (match (tt_c M x r).state with
    | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
    | none => tt_D M x r) = _
  rw [hq]

/-- **The invariant along the orbit** [HS66; AB09, §1.7]: at every time `r` the data are full
and represent the work tapes of `M`'s configuration after `r` steps.

**Proof sketch.** Induction on `r`. At `0` the tracks are empty and represent blank tapes
(`Turing.zoneTrackTape_empty`), as `M`'s initial work tapes are (`Turing.Cfg.init_workTapes`).
A live step is `tt_round_inv`, `M`'s next configuration being its step
(`Turing.MultiTapeTM.runFrom_succ_eq_step'`); a halted one changes neither side
(`Turing.MultiTapeTM.step_of_halt`). -/
private theorem tt_D_inv (M : FinTM Bool) (x : List Bool) (r : ℕ) :
    tt_fullD (tt_D M x r) ∧ tt_rep (tt_c M x r) (tt_D M x r) := by
  induction r with
  | zero =>
    refine ⟨fun _ => tt_full_empty, fun t p => ?_⟩
    show zoneTrackTape (ZoneContents.empty 0) p =
      (M.tm.runFrom (M.tm.initCfg x) 0).workTapes t _
    rw [zoneTrackTape_empty, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq,
      Cfg.init_workTapes]
  | succ r ih =>
    have hc : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
    cases hq : (tt_c M x r).state with
    | none =>
      rw [hc, MultiTapeTM.step_of_halt hq]
      show tt_fullD (match (tt_c M x r).state with
        | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
        | none => tt_D M x r) ∧ tt_rep (tt_c M x r) (match (tt_c M x r).state with
        | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
        | none => tt_D M x r)
      rw [hq]
      exact ih
    | some q =>
      rw [tt_D_succ M x r q hq, hc]
      exact (tt_round_inv M (tt_c M x r) q hq _ ih.1 ih.2).2

/-! ### The run: the configurations at the round boundaries and the iteration -/

/-- Moving input heads at equal positions over inputs of equal length gives equal positions. -/
private theorem tt_moveInputPos_val {n n' : ℕ} (hn : n = n') (p : Fin (n + 2)) (p' : Fin (n' + 2))
    (h : p.val = p'.val) (s : SignType) : (moveInputPos p s).val = (moveInputPos p' s).val := by
  subst hn
  rw [Fin.ext h]

/-- **The decoded input symbol** of a configuration on the encoded input `x.map Sum.inl` is the
input symbol of a configuration on `x` with the input head at the same position.

**Proof sketch.** Lift `c` along `Sum.inl` (`Turing.Cfg.liftSymbols`): the lift is on the
encoded input with `c`'s input head, so `d` reads what it reads (`Turing.Cfg.inputSymbol_congr`),
namely `c`'s input symbol mapped by `Sum.inl` (`Turing.Cfg.liftSymbols_inputSymbol`), which
`tt_decodeIn` decodes back. -/
private theorem tt_inputSymbol {k k' : ℕ} {S S' : Type} {x : List Bool}
    (d : Cfg k (ZoneSym k') S (x.map Sum.inl)) (c : Cfg k' Bool S' x)
    (h : d.inputPos.val = c.inputPos.val) : tt_decodeIn d.inputSymbol = c.inputSymbol := by
  rw [Cfg.inputSymbol_congr d (c.liftSymbols Function.Embedding.inl)
    (by rw [Cfg.liftSymbols_inputPos, Fin.coe_cast]; exact h), Cfg.liftSymbols_inputSymbol]
  cases c.inputSymbol <;> rfl

/-- The input position of `M`'s configuration on `x`, as a position on the encoded input. -/
private def tt_ipOf (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x) :
    Fin ((x.map (Sum.inl : Bool → ZoneSym M.k)).length + 2) :=
  ⟨c.inputPos.val, by rw [List.length_map]; exact c.inputPos.isLt⟩

/-- **The zone machine's configurations at the round boundaries** [HS66; AB09, §1.7]: its
initial configuration, and after `r + 1` rounds the transition step at `M`'s state after
`r + 1` steps, with the orbit's data, `M`'s input position and `M`'s output encoded. -/
private def tt_cs (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool) :
    ℕ → Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) (x.map Sum.inl)
  | 0 => Cfg.init ⟨none, .inl M.tm.q₀⟩ (x.map Sum.inl)
  | r + 1 => tt_cfg ((tt_c M x (r + 1)).state.map fun q => ⟨none, .inl q⟩) (tt_D M x (r + 1))
      (tt_ipOf M (tt_c M x (r + 1))) ((tt_c M x (r + 1)).output.map Sum.inl)

/-- **The length of round `r`**: two steps for the transition step and its dispatch, and each
track's phase with its dispatch step; `0` once `M` has halted. -/
private def tt_T (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool) (r : ℕ) : ℕ :=
  match (tt_c M x r).state with
  | some q =>
    2 + ∑ j ∈ Finset.range M.k, tt_τ M F (x.map Sum.inl)
      (tt_moves (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)))
      (tt_homeData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r))
      (moveInputPos (tt_ipOf M (tt_c M x r))
        (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)).inputTape)
      ((tt_c M x r).output.map Sum.inl ++
        ((tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)).output.map Sum.inl).toList) j
  | none => 0

/-- **A round's start is a transition-step configuration** of `tt_round`: at a live time `r`,
the boundary configuration is the transition step at `M`'s state, renamed into the host, with a
home cell that reads the orbit's homes (blank in the first round, the zoned tape's later).

**Proof sketch.** At `r = 0` the host's initial configuration (`Turing.Cfg.init`'s fields) has
blank tapes, which is the zoned tape of the empty contents off the home cell
(`Turing.zonedTape_blank_outside`, `Turing.zoneStart_eq`) with a blank home; a blank home reads
blank (`Turing.zoneCellOfCell_none`), as the empty contents' homes are. Later a boundary
configuration's home cell is the zoned tape's own (`Function.update_eq_self`), which reads the
homes (`Turing.zonedTape_zero`, `Turing.zoneCellOfCell_inr`). Field by field through
`Turing.Cfg.mapState_eq_of_fields`. -/
private theorem tt_cs_start (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool)
    (r : ℕ) (q : M.State) (hq : (tt_c M x r).state = some q) :
    ∃ h0 : Option (ZoneSym M.k), (∀ t, tt_homeRead h0 t = ((tt_D M x r).2 t).home) ∧
      tt_cs M F x r = (tt_cfg0 (some (.inl q)) (tt_D M x r) h0 (tt_ipOf M (tt_c M x r))
        ((tt_c M x r).output.map Sum.inl) :
          Cfg 2 (ZoneSym M.k) (tt_LeafSt M) (x.map Sum.inl)).mapState (Sigma.mk none) := by
  cases r with
  | zero =>
    have hc : tt_c M x 0 = Cfg.init M.tm.q₀ x := by
      show M.tm.runFrom (M.tm.initCfg x) 0 = _
      rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq]
    rw [hc, Cfg.init_state] at hq
    obtain rfl := Option.some.inj hq
    refine ⟨none, fun t => ?_, ?_⟩
    · show (zoneCellOfCell none t).join = (ZoneContents.empty 0).home
      rw [zoneCellOfCell_none, ZoneContents.empty_home]
      rfl
    · show Cfg.init (⟨none, .inl M.tm.q₀⟩ : Σ i, tt_Ph M F i) (x.map Sum.inl) = _
      refine (Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_).symm
      · rw [Cfg.init_state]
        rfl
      · rw [Cfg.init_inputPos]
        refine Fin.ext ?_
        show (tt_c M x 0).inputPos.val = _
        rw [hc, Cfg.init_inputPos]
        rfl
      · funext j p
        rw [Cfg.init_workTapes]
        by_cases hj : j = 0
        · subst hj
          show Function.update (zonedTape (fun _ => ZoneContents.empty 0)) 0 none p = none
          by_cases hp : p = 0
          · subst hp
            exact Function.update_self _ _ _
          · rw [Function.update_of_ne hp]
            refine zonedTape_blank_outside _ p ?_
            rw [zoneStart_eq]
            have : (1 : ℤ) ≤ |p| := Int.one_le_abs hp
            norm_num
            omega
        · show (if j = 0 then _ else fun _ => none) p = none
          rw [if_neg hj]
      · funext j
        rw [Cfg.init_workTapePos]
        rfl
      · rw [Cfg.init_output]
        show (tt_c M x 0).output.map Sum.inl = []
        rw [hc, Cfg.init_output, List.map_nil]
  | succ r =>
    refine ⟨zonedTape (tt_D M x (r + 1)).2 0, fun t => ?_, ?_⟩
    · rw [tt_homeRead, zonedTape_zero, zoneCellOfCell_inr]
      rfl
    · show tt_cfg _ _ _ _ = _
      rw [hq]
      apply Eq.symm
      refine Cfg.mapState_eq_of_fields _ _ _ rfl rfl ?_ rfl rfl
      funext j p
      by_cases hj : j = 0
      · subst hj
        show Function.update (zonedTape (tt_D M x (r + 1)).2) 0
          (zonedTape (tt_D M x (r + 1)).2 0) p = zonedTape (tt_D M x (r + 1)).2 p
        rw [Function.update_eq_self]
      · show (if j = 0 then _ else fun _ => none) p = (if j = 0 then _ else fun _ => none) p
        rw [if_neg hj, if_neg hj]

/-- **One round of the run** [HS66; AB09, §1.7]: while `M` is live after `r + 1` steps, the
zone machine runs live from the boundary configuration after `r` rounds to the one after
`r + 1`, in `tt_T` steps.

**Proof sketch.** `M` is live at `r` too (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`).
The start is a transition-step configuration (`tt_cs_start`), and the round's action is `M`'s
(`tt_round_inv`), whose successor state is `M`'s next state (`Turing.Action.apply_state`).
`tt_round` gives the segment; its endpoint is the next boundary configuration: the data are the
orbit's next (`tt_D_succ`), the input head moves as `M`'s (`tt_moveInputPos_val`,
`Turing.Action.apply_inputPos`) and the output gains the encoded emission
(`Turing.Action.apply_output`, `Option.toList_map`). -/
private theorem tt_cs_round (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (r : ℕ) (hr : (tt_c M x (r + 1)).state ≠ none) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cs M F x r) (tt_cs M F x (r + 1)) (tt_T M F x r) := by
  have hlive : (tt_c M x r).state ≠ none :=
    MultiTapeTM.runFrom_state_ne_none_of_le _ _ (r + 1) hr r (Nat.le_succ r)
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hr
  have hstep : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
  obtain ⟨hact, -, -⟩ := tt_round_inv M (tt_c M x r) q hq _ (tt_D_inv M x r).1 (tt_D_inv M x r).2
  set a := tt_act M q (tt_c M x r).inputSymbol (tt_D M x r) with ha
  have happly : tt_c M x (r + 1) = a.apply (tt_c M x r) := by
    rw [hstep, MultiTapeTM.step_of_some hq, ← hact]
  have hsa : a.state = some q' := by
    rw [← hq', happly, Action.apply_state]
  obtain ⟨h0, hread, hstart⟩ := tt_cs_start M F x r q hq
  have hinp : tt_decodeIn (tt_cfg0 (some (.inl q)) (tt_D M x r) h0 (tt_ipOf M (tt_c M x r))
      ((tt_c M x r).output.map Sum.inl) :
        Cfg 2 (ZoneSym M.k) (tt_LeafSt M) (x.map Sum.inl)).inputSymbol =
      (tt_c M x r).inputSymbol :=
    tt_inputSymbol _ _ rfl
  have H := (tt_round M F hk q (tt_D M x r) h0 hread (tt_ipOf M (tt_c M x r))
    ((tt_c M x r).output.map Sum.inl) _ hinp).2 q' hsa
  have hT : tt_T M F x r = 2 + ∑ j ∈ Finset.range M.k, tt_τ M F (x.map Sum.inl) (tt_moves a)
      (tt_homeData a (tt_D M x r)) (moveInputPos (tt_ipOf M (tt_c M x r)) a.inputTape)
      ((tt_c M x r).output.map Sum.inl ++ (a.output.map Sum.inl).toList) j := by
    show (match (tt_c M x r).state with
      | some q => _
      | none => 0) = _
    rw [hq]
  have hend : tt_cs M F x (r + 1) = tt_cfg (some ⟨none, .inl q'⟩)
      (tt_Dtr (tt_moves a) (tt_homeData a (tt_D M x r)) M.k)
      (moveInputPos (tt_ipOf M (tt_c M x r)) a.inputTape)
      ((tt_c M x r).output.map Sum.inl ++ (a.output.map Sum.inl).toList) := by
    show tt_cfg _ _ _ _ = _
    rw [hq', tt_D_succ M x r q hq]
    congr 1
    · refine Fin.ext ?_
      show (tt_c M x (r + 1)).inputPos.val = _
      rw [happly, Action.apply_inputPos]
      exact tt_moveInputPos_val (List.length_map _).symm _ _ rfl _
    · rw [happly, Action.apply_output, List.map_append, Option.toList_map]
  rw [hstart, hT, hend]
  exact H

/-- **The run through the first `s` rounds** [HS66; AB09, §1.7]: while `M` is live after `s`
steps, the zone machine runs live from its initial configuration to the boundary configuration
after `s` rounds, in the rounds' summed time.

**Proof sketch.** `Turing.Segment.iterate_seq` over the rounds (`tt_cs_round`), each round's
liveness from `M`'s at `s` (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). -/
private theorem tt_cs_run (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (s : ℕ) (hs : (tt_c M x s).state ≠ none) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cs M F x 0) (tt_cs M F x s)
      (∑ r ∈ Finset.range s, tt_T M F x r) :=
  Segment.iterate_seq (tt_cs M F x) (tt_T M F x) trivial s fun r hr =>
    tt_cs_round M F hk x r (MultiTapeTM.runFrom_state_ne_none_of_le _ _ s hs (r + 1) hr)

/-- **The halting round** [HS66; AB09, §1.7]: if `M` is live after `r` steps and halted after
`r + 1`, the zone machine halts one step after the boundary configuration of round `r`, with
`M`'s output encoded.

**Proof sketch.** The start is a transition-step configuration (`tt_cs_start`); the round's
action is `M`'s (`tt_round_inv`) and halts with it; `tt_round`'s halting clause gives the halt
and the output, which is `M`'s after its last step (`Turing.Action.apply_output`). -/
private theorem tt_cs_halt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (r : ℕ) (hr : (tt_c M x r).state ≠ none)
    (hh : (tt_c M x (r + 1)).state = none) :
    ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x r) 1).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x r) 1).output = (tt_c M x (r + 1)).output.map Sum.inl := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hr
  have hstep : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
  obtain ⟨hact, -, -⟩ := tt_round_inv M (tt_c M x r) q hq _ (tt_D_inv M x r).1 (tt_D_inv M x r).2
  set a := tt_act M q (tt_c M x r).inputSymbol (tt_D M x r) with ha
  have happly : tt_c M x (r + 1) = a.apply (tt_c M x r) := by
    rw [hstep, MultiTapeTM.step_of_some hq, ← hact]
  have hsa : a.state = none := by
    rw [← hh, happly, Action.apply_state]
  obtain ⟨h0, hread, hstart⟩ := tt_cs_start M F x r q hq
  have H := (tt_round M F hk q (tt_D M x r) h0 hread (tt_ipOf M (tt_c M x r))
    ((tt_c M x r).output.map Sum.inl) _ (tt_inputSymbol _ _ rfl)).1 hsa
  rw [hstart]
  refine ⟨H.1, ?_⟩
  rw [H.2, happly, Action.apply_output, List.map_append, Option.toList_map]

/-- **Every round takes at least two steps** while `M` is live: the transition step and its
dispatch. -/
private theorem tt_T_ge (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool) (r : ℕ)
    (hr : (tt_c M x r).state ≠ none) : 2 ≤ tt_T M F x r := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hr
  show 2 ≤ (match (tt_c M x r).state with
    | some q => _
    | none => 0)
  rw [hq]
  exact Nat.le_add_right _ _

/-- The zone machine's initial configuration is the boundary configuration before any round. -/
private theorem tt_HS_init (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) : (tt_HS M F hk).tm.initCfg (x.map Sum.inl) = tt_cs M F x 0 := by
  show (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).initCfg (x.map Sum.inl) =
    Cfg.init ⟨none, .inl M.tm.q₀⟩ (x.map Sum.inl)
  rw [MultiTapeTM.initCfg_eq, phaseHostTM_q₀]

/-- **The zone machine reproduces a halting run** [HS66; AB09, §1.7]: if `M` halts on `x`
within `t` steps with output `o`, it first halts at some `t₀ ≤ t`, live before, and the zone
machine halts on `x.map Sum.inl` with `o.map Sum.inl` after the first `t₀ - 1` rounds and one
more step.

**Proof sketch.** The first halt (`Turing.MultiTapeTM.exists_first_halt`) is positive, as the
initial configuration is live. The rounds before it run as one segment (`tt_cs_run`), and the
last transition halts (`tt_cs_halt`) with `M`'s output, which is `o`; the two concatenate by
`Turing.MultiTapeTM.runFrom_add`. -/
private theorem tt_forward_run (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x o : List Bool) (t : ℕ) (h : M.ComputesInTime x o t) :
    ∃ t₀, t₀ ≤ t ∧ 1 ≤ t₀ ∧ (∀ r < t₀, (tt_c M x r).state ≠ none) ∧
      (tt_HS M F hk).ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
        (∑ r ∈ Finset.range (t₀ - 1), tt_T M F x r + 1) := by
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x o t).1 h
  obtain ⟨u, hu, hlive, heq⟩ := MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) hs
  have hc : ∀ r, tt_c M x r = M.tm.runFrom (M.tm.initCfg x) r := fun _ => rfl
  cases u with
  | zero =>
    exfalso
    have h0 : (M.tm.runFrom (M.tm.initCfg x) 0).state = none := heq ▸ hs
    exact not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)
  | succ s =>
    have hl : ∀ r < s + 1, (tt_c M x r).state ≠ none := fun r hr => hlive r hr
    refine ⟨s + 1, hu, Nat.le_add_left 1 s, hl, ?_⟩
    rw [Nat.add_sub_cancel]
    have hseg := tt_cs_run M F hk x s (hl s (Nat.lt_succ_self s))
    have hhalt : (tt_c M x (s + 1)).state = none := by rw [hc, heq]; exact hs
    obtain ⟨h1, h2⟩ := tt_cs_halt M F hk x s (hl s (Nat.lt_succ_self s)) hhalt
    rw [segment_iff] at hseg
    rw [computesInTime_iff, tt_HS_init]
    show ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x 0) _).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x 0) _).output = _
    rw [MultiTapeTM.runFrom_add, hseg.1]
    refine ⟨h1, ?_⟩
    rw [h2, hc, heq, ho]

/-- **Every completed output of the zone machine is an encoded output of `M`** [HS66; AB09,
§1.7].

**Proof sketch.** If `M` never halted on `x`, the first `t' + 1` rounds would run live for at
least `2 (t' + 1)` steps (`tt_cs_run`, `tt_T_ge`), so the zone machine would be live at `t'`.
Hence `M` halts at some time with some output `v`; then the zone machine halts with
`v.map Sum.inl` (`tt_forward_run`), and a completed output is unique
(`Turing.FinTM.ComputesInTime.output_unique`). -/
private theorem tt_converse (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ)
    (h : (tt_HS M F hk).ComputesInTime (x.map Sum.inl) o' t') :
    ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl := by
  by_cases hhalt : ∃ s, (tt_c M x s).state = none
  · obtain ⟨s, hs⟩ := hhalt
    have hM : M.ComputesInTime x (tt_c M x s).output s :=
      (computesInTime_iff M x _ s).2 ⟨hs, rfl⟩
    obtain ⟨_, -, -, -, hHS⟩ := tt_forward_run M F hk x _ s hM
    exact ⟨s, _, hM, h.output_unique hHS⟩
  · exfalso
    push_neg at hhalt
    have hseg := tt_cs_run M F hk x (t' + 1) (hhalt _)
    have hsum : 2 * (t' + 1) ≤ ∑ r ∈ Finset.range (t' + 1), tt_T M F x r := by
      have h := Finset.card_nsmul_le_sum (Finset.range (t' + 1)) (tt_T M F x) 2
        fun r _ => tt_T_ge M F x r (hhalt r)
      rwa [Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm (t' + 1) 2] at h
    obtain ⟨hs, -⟩ := (computesInTime_iff _ _ _ _).1 h
    rw [tt_HS_init] at hs
    exact (segment_iff _ _ _ _ _ _).1 hseg |>.2.1 t' (by omega) (Set.mem_singleton_iff.mpr hs)

/-! ### Side totals -/

/-- **The side total** of one track below level `n`: the number of cells stored in its right
zones of levels `< n` (levels not laid out count `0`). -/
private def tt_rsum {ℓ : ℕ} (z : ZoneContents ℓ) (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.range n, if h : l < ℓ then (z.right ⟨l, h⟩).length else 0

/-- One more level of the side total. -/
private theorem tt_rsum_succ {ℓ : ℕ} (z : ZoneContents ℓ) (n : ℕ) (hn : n < ℓ) :
    tt_rsum z (n + 1) = tt_rsum z n + (z.right ⟨n, hn⟩).length := by
  rw [tt_rsum, Finset.sum_range_succ, dif_pos hn]
  rfl

/-- **Below the scanned index, the side total is extreme** [AB09, §1.7]: under fullness, below
the scanned index `j` of a move in direction `dir` the feeding zones are empty, so the right
zones of levels `< n ≤ j` hold nothing (a right move) or everything (a left move:
`2^{n+1} − 2` cells).

**Proof sketch.** Induction on `n`: the level `n < j` is empty on the feeding side
(`Turing.zoneShiftIndex_empty`), so by fullness its right zone holds `0` cells (a right move) or
the whole capacity `2 · 2^n` (a left move), and `2^{n+1} − 2 + 2^{n+1} = 2^{n+2} − 2`. -/
private theorem tt_rsum_low {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (hz : tt_full z) (n : ℕ)
    (hn : n ≤ zoneShiftIndex dir z) (hnℓ : n ≤ ℓ) :
    tt_rsum z n = if dir then 0 else 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => cases dir <;> rfl
  | succ n ih =>
    rw [tt_rsum_succ z n (by omega), ih (by omega) (by omega)]
    have he := zoneShiftIndex_empty dir z ⟨n, by omega⟩ (by show n < _; omega)
    cases dir
    · rw [ZoneContents.words_false] at he
      have hs := (hz ⟨n, by omega⟩).1
      rw [he, List.length_nil, zero_add, zoneCapacity_eq] at hs
      show 2 ^ (n + 1) - 2 + (z.right ⟨n, _⟩).length = 2 ^ (n + 1 + 1) - 2
      have h1 : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
      rw [show (z.right ⟨n, _⟩).length = 2 * 2 ^ n from hs, pow_succ, pow_succ]
      rw [pow_succ] at h1
      omega
    · rw [ZoneContents.words_true] at he
      show 0 + (z.right ⟨n, _⟩).length = 0
      rw [he]
      rfl

/-- **A right rebalance moves one cell off the right side** [AB09, §1.7]: under fullness, with
scanned index `j < ℓ`, the rebalanced side total below `n` is `2^n − 1` for `n ≤ j` (the levels
below `j` half full), and one less than before for `j < n ≤ ℓ`.

**Proof sketch.** Induction on `n`, reading the levels through `tt_full_rebalance_true` below
`j`, `Turing.zoneCascadeRight_lengths` at `j` under the pre-state `tt_full_pre_true` (the donor
loses `2^j` cells, which fill the `2^j − 1` cells below and the home), and
`Turing.zoneRebalance_frame` above `j`. -/
private theorem tt_rsum_rebalance_true {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex true z < ℓ) (n : ℕ) (hnℓ : n ≤ ℓ) :
    (n ≤ zoneShiftIndex true z → tt_rsum (zoneRebalance true z) n = 2 ^ n - 1) ∧
      (zoneShiftIndex true z < n → tt_rsum (zoneRebalance true z) n + 1 = tt_rsum z n) := by
  set j := zoneShiftIndex true z with hj
  obtain ⟨hr, hl, hdonor, hroom⟩ := tt_full_pre_true z hz hj.symm h
  have hlow := (tt_full_rebalance_true z hz h).2
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame true z k hk
  have hz0 := tt_rsum_low true z hz j le_rfl h.le
  have hcas := zoneCascadeRight_lengths j h z hr hl hdonor hroom
  clear hr
  induction n with
  | zero => exact ⟨fun _ => rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    rw [tt_rsum_succ _ n (by omega), tt_rsum_succ z n (by omega)]
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [ih₁ (by omega), (hlow ⟨n, by omega⟩ (by show n < j; omega)).2]
      show 2 ^ n - 1 + 2 ^ n = 2 ^ (n + 1) - 1
      have := Nat.one_le_two_pow (n := n)
      rw [pow_succ]
      omega
    · rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [(hframe ⟨n, by omega⟩ hjn).2, ← ih₂ hjn]
        omega
      · have hnj : n = j := by omega
        have hfin : (⟨n, (by omega : n < ℓ)⟩ : Fin ℓ) = ⟨j, h⟩ := Fin.ext hnj
        obtain ⟨-, hjr, -⟩ := hcas
        have hj' : ((zoneRebalance true z).right ⟨j, h⟩).length =
            (z.right ⟨j, h⟩).length - 2 ^ j := by
          rw [zoneRebalance_of_lt true z h, zoneCascade_true]
          exact hjr
        have hz0' : tt_rsum z j = 0 := by rw [hz0]; rfl
        rw [hfin, ih₁ hnj.le, hnj, hz0', hj']
        have := Nat.one_le_two_pow (n := j)
        omega

/-- **A left rebalance moves one cell onto the right side**: the mirror of
`tt_rsum_rebalance_true`; the side total below `n ≤ j` is `2^n − 1`, and for `j < n ≤ ℓ` it is
one more than before.

**Proof sketch.** As for `tt_rsum_rebalance_true`, with `tt_full_rebalance_false` below the
index, `Turing.zoneCascadeLeft_lengths` at it under the pre-state `tt_full_pre_false` (the right
zone gains `2^j` cells, while the right zones below drop from full to half: `2^{j+1} − 2` cells
become `2^j − 1`), and `Turing.zoneRebalance_frame` above. -/
private theorem tt_rsum_rebalance_false {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex false z < ℓ) (n : ℕ) (hnℓ : n ≤ ℓ) :
    (n ≤ zoneShiftIndex false z → tt_rsum (zoneRebalance false z) n = 2 ^ n - 1) ∧
      (zoneShiftIndex false z < n → tt_rsum (zoneRebalance false z) n = tt_rsum z n + 1) := by
  set j := zoneShiftIndex false z with hj
  obtain ⟨hl, hr, hdonor, hroom⟩ := tt_full_pre_false z hz hj.symm h
  have hlow := (tt_full_rebalance_false z hz h).2
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame false z k hk
  have hz0 := tt_rsum_low false z hz j le_rfl h.le
  have hcas := zoneCascadeLeft_lengths j h z hl hr hdonor hroom
  clear hl
  induction n with
  | zero => exact ⟨fun _ => rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    rw [tt_rsum_succ _ n (by omega), tt_rsum_succ z n (by omega)]
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [ih₁ (by omega), (hlow ⟨n, by omega⟩ (by show n < j; omega)).2]
      show 2 ^ n - 1 + 2 ^ n = 2 ^ (n + 1) - 1
      have := Nat.one_le_two_pow (n := n)
      rw [pow_succ]
      omega
    · rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [(hframe ⟨n, by omega⟩ hjn).2, ih₂ hjn]
        omega
      · have hnj : n = j := by omega
        have hfin : (⟨n, (by omega : n < ℓ)⟩ : Fin ℓ) = ⟨j, h⟩ := Fin.ext hnj
        obtain ⟨-, -, hjr⟩ := hcas
        have hj' : ((zoneRebalance false z).right ⟨j, h⟩).length =
            (z.right ⟨j, h⟩).length + 2 ^ j := by
          rw [zoneRebalance_of_lt false z h, zoneCascade_false]
          exact hjr
        have hz0' : tt_rsum z j = 2 ^ (j + 1) - 2 := by rw [hz0]; rfl
        rw [hfin, ih₁ hnj.le, hnj, hz0', hj']
        have := Nat.one_le_two_pow (n := j)
        rw [pow_succ]
        omega

/-- The home write keeps every side total. -/
private theorem tt_rsum_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool) (n : ℕ) :
    tt_rsum (zoneHomeWrite z v) n = tt_rsum z n := by
  unfold tt_rsum
  simp only [zoneHomeWrite_right]

/-- **The extension keeps the side totals of the old levels and adds `2^ℓ` at the new one**
(`Turing.ZoneContents.extend_words_castSucc`, `_last`). -/
private theorem tt_rsum_extend {ℓ : ℕ} (z : ZoneContents ℓ) :
    (∀ n ≤ ℓ, tt_rsum z.extend n = tt_rsum z n) ∧
      tt_rsum z.extend (ℓ + 1) = tt_rsum z ℓ + 2 ^ ℓ := by
  have hold : ∀ n ≤ ℓ, tt_rsum z.extend n = tt_rsum z n := by
    intro n hn
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l < ℓ := by have := Finset.mem_range.mp hl; omega
    rw [dif_pos hl', dif_pos (by omega)]
    have := ZoneContents.extend_words_castSucc true z ⟨l, hl'⟩
    rw [ZoneContents.words_true, ZoneContents.words_true] at this
    exact congrArg List.length this
  refine ⟨hold, ?_⟩
  rw [tt_rsum_succ _ ℓ (Nat.lt_succ_self ℓ), hold ℓ le_rfl]
  have := ZoneContents.extend_words_last true z
  rw [ZoneContents.words_true] at this
  rw [show (⟨ℓ, Nat.lt_succ_self ℓ⟩ : Fin (ℓ + 1)) = Fin.last ℓ from rfl, this,
    List.length_replicate]

/-- **One track's step on the side totals** [AB09, §1.7]. Under fullness, with `j` the scanned
index of track `t`'s step in direction `dir` and `ℓ = D.1`:
* track `t`'s side totals below `n ≤ min ℓ j` become `2^n − 1`;
* for `j < n ≤ ℓ` they move by the head's displacement (`tt_shift dir` cells leave the right
  side);
* its whole side total moves by the displacement, plus `2^ℓ` after an extension;
* every other track keeps its side totals below `ℓ`, and its whole side total gains `2^ℓ` after
  an extension;
* the level count is `ℓ`, or `ℓ + 1` after an extension.

**Proof sketch.** With a nonempty feeding zone (`Turing.zoneTrackStepData_of_lt`,
`Turing.zoneRebalanceData_eq`) this is `tt_rsum_rebalance_true`/`_false` on track `t` and
`Function.update_of_ne` elsewhere. Otherwise (`Turing.zoneTrackStepData_of_not_lt`,
`Turing.zoneExtendData_eq`) the scanned index is `ℓ`, every track is extended
(`tt_rsum_extend`), and track `t` is rebalanced at the new level `ℓ`
(`Turing.zoneShiftIndex_extend`, `tt_full_extend`). -/
private theorem tt_trackStep_rsum {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k)
    (hD : tt_fullD D) :
    (∀ n, n ≤ D.1 → n ≤ zoneRebalanceIndex dir t D →
      tt_rsum ((zoneTrackStepData dir t D).2 t) n = 2 ^ n - 1) ∧
    (∀ n, n ≤ D.1 → zoneRebalanceIndex dir t D < n →
      (tt_rsum ((zoneTrackStepData dir t D).2 t) n : ℤ) = tt_rsum (D.2 t) n - tt_shift dir) ∧
    ((tt_rsum ((zoneTrackStepData dir t D).2 t) (zoneTrackStepData dir t D).1 : ℤ) =
      tt_rsum (D.2 t) D.1 - tt_shift dir +
        (if zoneRebalanceIndex dir t D < D.1 then 0 else 2 ^ D.1)) ∧
    (∀ t', t' ≠ t →
      (∀ n, n ≤ D.1 → tt_rsum ((zoneTrackStepData dir t D).2 t') n = tt_rsum (D.2 t') n) ∧
      tt_rsum ((zoneTrackStepData dir t D).2 t') (zoneTrackStepData dir t D).1 =
        tt_rsum (D.2 t') D.1 + (if zoneRebalanceIndex dir t D < D.1 then 0 else 2 ^ D.1)) ∧
    (zoneTrackStepData dir t D).1 =
      (if zoneRebalanceIndex dir t D < D.1 then D.1 else D.1 + 1) := by
  have hreb : ∀ {ℓ : ℕ} (z : ZoneContents ℓ), tt_full z → zoneShiftIndex dir z < ℓ →
      ∀ n, n ≤ ℓ → (n ≤ zoneShiftIndex dir z → tt_rsum (zoneRebalance dir z) n = 2 ^ n - 1) ∧
        (zoneShiftIndex dir z < n →
          (tt_rsum (zoneRebalance dir z) n : ℤ) = tt_rsum z n - tt_shift dir) := by
    intro ℓ z hz h n hn
    cases dir
    · obtain ⟨h1, h2⟩ := tt_rsum_rebalance_false z hz h n hn
      refine ⟨h1, fun h' => ?_⟩
      rw [h2 h']
      push_cast
      show _ = _ - (-1 : ℤ)
      ring
    · obtain ⟨h1, h2⟩ := tt_rsum_rebalance_true z hz h n hn
      refine ⟨h1, fun h' => ?_⟩
      rw [← h2 h']
      push_cast
      show _ = _ - (1 : ℤ)
      ring
  rw [zoneRebalanceIndex_eq]
  by_cases hlt : zoneShiftIndex dir (D.2 t) < D.1
  · have hlt' : zoneRebalanceIndex dir t D < D.1 := by rwa [zoneRebalanceIndex_eq]
    rw [zoneTrackStepData_of_lt dir t hlt', zoneRebalanceData_eq]
    simp only [if_pos hlt, Function.update_self]
    refine ⟨fun n hn hj => (hreb _ (hD t) hlt n hn).1 hj,
      fun n hn hj => (hreb _ (hD t) hlt n hn).2 hj, ?_, fun t' ht' => ?_, trivial⟩
    · rw [(hreb _ (hD t) hlt D.1 le_rfl).2 hlt, add_zero]
    · rw [Function.update_of_ne ht', add_zero]
      exact ⟨fun _ _ => rfl, rfl⟩
  · have hlt' : ¬ zoneRebalanceIndex dir t D < D.1 := by rwa [zoneRebalanceIndex_eq]
    have hidx : zoneShiftIndex dir (D.2 t) = D.1 :=
      eq_of_le_of_not_lt (zoneShiftIndex_le dir (D.2 t)) hlt
    have hidx' := zoneShiftIndex_extend dir (D.2 t) hidx
    have hfull' := tt_full_extend _ (hD t)
    have hlt₂ : zoneShiftIndex dir (D.2 t).extend < D.1 + 1 := by
      rw [hidx']
      exact Nat.lt_succ_self _
    rw [zoneTrackStepData_of_not_lt dir t hlt', zoneRebalanceData_eq, zoneExtendData_eq]
    simp only [if_neg hlt, Function.update_self]
    refine ⟨fun n hn _ => (hreb _ hfull' hlt₂ n (by omega)).1 (by rw [hidx']; exact hn),
      fun n hn hj => absurd hj (by rw [hidx]; omega), ?_, fun t' ht' => ?_, trivial⟩
    · rw [(hreb _ hfull' hlt₂ (D.1 + 1) le_rfl).2 (by rw [hidx']; exact Nat.lt_succ_self _),
        (tt_rsum_extend (D.2 t)).2]
      push_cast
      ring
    · rw [Function.update_of_ne ht']
      exact ⟨fun n hn => (tt_rsum_extend (D.2 t')).1 n hn, (tt_rsum_extend (D.2 t')).2⟩

/-! ### Side totals through a round -/

/-- The tracks' steps never lower the level count. -/
private theorem tt_Dtr_level_mono {k : ℕ} (m : Fin k → SignType) (H : ZoneData k) (j₁ : ℕ) :
    ∀ j₂, j₁ ≤ j₂ → (tt_Dtr m H j₁).1 ≤ (tt_Dtr m H j₂).1 := by
  refine fun j₂ hj => monotone_nat_of_le_succ (f := fun j => (tt_Dtr m H j).1) (fun j => ?_) hj
  show (tt_Dtr m H j).1 ≤ (tt_Dtr m H (j + 1)).1
  by_cases h : j < k
  · rw [show tt_Dtr m H (j + 1) = tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) from dif_pos h]
    by_cases h0 : m ⟨j, h⟩ = 0
    · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) = tt_Dtr m H j from if_pos h0]
    · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) =
        zoneTrackStepData (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩ (tt_Dtr m H j) from if_neg h0]
      by_cases hlt : zoneRebalanceIndex (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩ (tt_Dtr m H j) <
          (tt_Dtr m H j).1
      · rw [zoneTrackStepData_of_lt _ _ hlt, zoneRebalanceData_eq]
      · rw [zoneTrackStepData_of_not_lt _ _ hlt, zoneRebalanceData_eq, zoneExtendData_eq]
        exact Nat.le_succ _
  · rw [show tt_Dtr m H (j + 1) = tt_Dtr m H j from dif_neg h]

/-- **The other tracks' steps keep a track's side totals** below a laid-out level `n`: from
`j₁` to `j₂` the steps of tracks other than `t` change no side total of track `t` below `n`. -/
private theorem tt_Dtr_other {k : ℕ} (m : Fin k → SignType) (H : ZoneData k) (hH : tt_fullD H)
    (t : Fin k) (n j₁ : ℕ) (hn : n ≤ (tt_Dtr m H j₁).1) :
    ∀ j₂, j₁ ≤ j₂ → (t.val < j₁ ∨ j₂ ≤ t.val) →
      tt_rsum ((tt_Dtr m H j₂).2 t) n = tt_rsum ((tt_Dtr m H j₁).2 t) n := by
  intro j₂ hj
  induction j₂, hj using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ j hj ih =>
    intro hc
    rw [← ih (by omega)]
    have hlev := tt_Dtr_level_mono m H j₁ j hj
    by_cases h : j < k
    · rw [show tt_Dtr m H (j + 1) = tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) from dif_pos h]
      by_cases h0 : m ⟨j, h⟩ = 0
      · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) = tt_Dtr m H j from if_pos h0]
      · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) =
          zoneTrackStepData (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩ (tt_Dtr m H j) from if_neg h0]
        have ht : t ≠ ⟨j, h⟩ := fun he => by rw [he] at hc; simp at hc; omega
        exact ((tt_trackStep_rsum _ _ _ (tt_Dtr_inv m H hH j).1).2.2.2.1 t ht).1 n (by omega)
    · rw [show tt_Dtr m H (j + 1) = tt_Dtr m H j from dif_neg h]

/-- The scanned index of track `t`'s step in the round with action `a` from data `D`. -/
private def tt_idxA {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) (t : Fin k) : ℕ :=
  tt_idx (tt_moves a t) t (tt_Dtr (tt_moves a) (tt_homeData a D) t.val)

/-- Track `t`'s own step in a round: the data after it are its step from the data before. -/
private theorem tt_Dtr_own {k : ℕ} (m : Fin k → SignType) (H : ZoneData k) (t : Fin k) :
    tt_Dtr m H (t.val + 1) = tt_trackData (m t) t (tt_Dtr m H t.val) :=
  dif_pos t.isLt

/-- **One round on track `t`'s side totals below a level `n ≥ 1`** [AB09, §1.7]. With `D` full,
the round's action `a`, its data `D'` and track `t`'s scanned index `i₀`:
* if `n ≤ i₀`, then `D'` has its levels below `n` laid out and half full on track `t`: the side
  total below `n` is `2^n − 1`;
* if `n ≤ D.1` and `n ≤ i₀`, the side total below `n` before the round is `0` or `2^{n+1} − 2`;
* if `n ≤ D.1` and `i₀ < n`, the round changes it by at most one;
* the level count never drops, and bounds `i₀` after the round.

**Proof sketch.** The home write and the other tracks' steps keep track `t`'s side totals below
a laid-out level (`tt_rsum_homeWrite`, `tt_Dtr_other`); track `t`'s own step is
`tt_trackStep_rsum` (a stay changes nothing and has index `0`), and the scanned zones below a
large index are empty or full (`tt_rsum_low`). -/
private theorem tt_round_rsum {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k)
    (hD : tt_fullD D) (t : Fin k) (n : ℕ) (hn1 : 1 ≤ n) :
    (n ≤ tt_idxA a D t → tt_rsum ((tt_roundData a D).2 t) n = 2 ^ n - 1 ∧
      n ≤ (tt_roundData a D).1) ∧
    (n ≤ D.1 → n ≤ tt_idxA a D t →
      tt_rsum (D.2 t) n = 0 ∨ tt_rsum (D.2 t) n = 2 ^ (n + 1) - 2) ∧
    (n ≤ D.1 → tt_idxA a D t < n →
      (tt_rsum ((tt_roundData a D).2 t) n : ℤ) ≤ tt_rsum (D.2 t) n + 1 ∧
        (tt_rsum (D.2 t) n : ℤ) ≤ tt_rsum ((tt_roundData a D).2 t) n + 1) ∧
    D.1 ≤ (tt_roundData a D).1 ∧ tt_idxA a D t ≤ (tt_roundData a D).1 := by
  set m := tt_moves a with hm
  set H := tt_homeData a D with hH
  have hHf : tt_fullD H := (tt_homeData_inv a D hD).1
  have hH1 : H.1 = D.1 := rfl
  have hHr : ∀ n, tt_rsum (H.2 t) n = tt_rsum (D.2 t) n := fun n => tt_rsum_homeWrite _ _ n
  set E := tt_Dtr m H t.val with hE
  have hEf : tt_fullD E := (tt_Dtr_inv m H hHf t.val).1
  have hEl : D.1 ≤ E.1 := tt_Dtr_level_mono m H 0 t.val (Nat.zero_le _)
  have hE'l : E.1 ≤ (tt_Dtr m H (t.val + 1)).1 := tt_Dtr_level_mono m H _ _ (Nat.le_succ _)
  have hDl : (tt_Dtr m H (t.val + 1)).1 ≤ (tt_roundData a D).1 :=
    tt_Dtr_level_mono m H _ k t.isLt
  have hEr : n ≤ D.1 → tt_rsum (E.2 t) n = tt_rsum (D.2 t) n := fun hnD => by
    rw [hE, tt_Dtr_other m H hHf t n 0 hnD t.val (Nat.zero_le _) (Or.inr le_rfl)]
    exact hHr n
  have hD'r : n ≤ (tt_Dtr m H (t.val + 1)).1 → tt_rsum ((tt_roundData a D).2 t) n =
      tt_rsum ((tt_Dtr m H (t.val + 1)).2 t) n := fun hn =>
    tt_Dtr_other m H hHf t n (t.val + 1) hn k t.isLt (Or.inl (Nat.lt_succ_self _))
  have hown := tt_Dtr_own m H t
  have hidx : tt_idxA a D t = tt_idx (m t) t E := rfl
  by_cases h0 : m t = 0
  · have hi0 : tt_idxA a D t = 0 := by rw [hidx]; exact if_pos h0
    rw [show tt_trackData (m t) t E = E from if_pos h0] at hown
    refine ⟨fun h => absurd h (by omega), fun _ h => absurd h (by omega), fun hnD _ => ?_,
      by rw [← hH1]; exact hEl.trans (hE'l.trans hDl), by rw [hi0]; exact Nat.zero_le _⟩
    rw [hD'r (by rw [hown]; omega), hown, hEr hnD]
    constructor <;> omega
  · set dir := tt_dir (m t)
    have hi : tt_idxA a D t = zoneRebalanceIndex dir t E := by rw [hidx]; exact if_neg h0
    rw [show tt_trackData (m t) t E = zoneTrackStepData dir t E from if_neg h0] at hown
    obtain ⟨c1, c2, -, -, -⟩ := tt_trackStep_rsum dir t E hEf
    have hiE : zoneRebalanceIndex dir t E ≤ E.1 := zoneRebalanceIndex_le dir t E
    refine ⟨fun hni => ?_, fun hnD hni => ?_, fun hnD hni => ?_,
      by rw [← hH1]; exact hEl.trans (hE'l.trans hDl), ?_⟩
    · rw [hi] at hni
      have hlev : n ≤ (tt_Dtr m H (t.val + 1)).1 := (hni.trans hiE).trans hE'l
      refine ⟨?_, hlev.trans hDl⟩
      rw [hD'r hlev, hown]
      exact c1 n (hni.trans hiE) hni
    · rw [← hEr hnD]
      rw [hi, zoneRebalanceIndex_eq] at hni
      have hl := tt_rsum_low dir (E.2 t) (hEf t) n hni (by omega)
      cases hdir : dir
      · rw [hdir, if_neg (by simp)] at hl
        exact Or.inr hl
      · rw [hdir, if_pos rfl] at hl
        exact Or.inl hl
    · rw [hi] at hni
      have hlev : n ≤ (tt_Dtr m H (t.val + 1)).1 := by omega
      rw [hD'r hlev, hown, c2 n (by omega) hni, hEr hnD]
      have : tt_shift dir = 1 ∨ tt_shift dir = -1 := by cases dir <;> simp [tt_shift]
      rcases this with hs | hs <;> rw [hs] <;> constructor <;> omega
    · rw [hi]
      exact hiE.trans (hE'l.trans hDl)

/-! ### Counting the expensive steps -/

/-- **Sparse sets of times are small**: a set of times below `T` any two of which are at least
`g ≥ 1` apart has at most `T / g + 1` elements.

**Proof sketch.** Division by `g` is injective on the set, since two of its elements differ by
at least `g`, and maps it into `{0, …, T / g}`. -/
private theorem tt_card_le_of_gap (T g : ℕ) (hg : 0 < g) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a < T) (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → a + g ≤ b) :
    S.card ≤ T / g + 1 := by
  have hstep : ∀ a ∈ S, ∀ b ∈ S, a < b → a / g < b / g := by
    intro a ha b hb hab
    have h := hgap a ha b hb hab
    calc a / g < a / g + 1 := Nat.lt_succ_self _
      _ = (a + g) / g := (Nat.add_div_right a hg).symm
      _ ≤ b / g := Nat.div_le_div_right h
  have hinj : Set.InjOn (fun a => a / g) S := StrictMonoOn.injOn hstep
  calc S.card ≤ (Finset.range (T / g + 1)).card :=
        Finset.card_le_card_of_injOn (fun a => a / g) (fun a ha =>
          Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hS a ha).le))) hinj
    _ = T / g + 1 := Finset.card_range _

/-! ### The count and level bounds over the run -/

/-- The scanned index of track `t`'s step in round `r` of the simulation of `M` on `x`
(`0` once `M` has halted). -/
private def tt_idxR (M : FinTM Bool) (x : List Bool) (t : Fin M.k) (r : ℕ) : ℕ :=
  match (tt_c M x r).state with
  | some q => tt_idxA (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r) t
  | none => 0

/-- **Track `t`'s side totals below `n ≥ 1` over one round of the run**: `tt_round_rsum` at a
live time. -/
private theorem tt_orbit_rsum (M : FinTM Bool) (x : List Bool) (r : ℕ)
    (hr : (tt_c M x r).state ≠ none) (t : Fin M.k) (n : ℕ) (hn1 : 1 ≤ n) :
    (n ≤ tt_idxR M x t r → tt_rsum ((tt_D M x (r + 1)).2 t) n = 2 ^ n - 1 ∧
      n ≤ (tt_D M x (r + 1)).1) ∧
    (n ≤ (tt_D M x r).1 → n ≤ tt_idxR M x t r →
      tt_rsum ((tt_D M x r).2 t) n = 0 ∨ tt_rsum ((tt_D M x r).2 t) n = 2 ^ (n + 1) - 2) ∧
    (n ≤ (tt_D M x r).1 → tt_idxR M x t r < n →
      (tt_rsum ((tt_D M x (r + 1)).2 t) n : ℤ) ≤ tt_rsum ((tt_D M x r).2 t) n + 1 ∧
        (tt_rsum ((tt_D M x r).2 t) n : ℤ) ≤ tt_rsum ((tt_D M x (r + 1)).2 t) n + 1) ∧
    (tt_D M x r).1 ≤ (tt_D M x (r + 1)).1 ∧ tt_idxR M x t r ≤ (tt_D M x (r + 1)).1 := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hr
  have hidx : tt_idxR M x t r =
      tt_idxA (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r) t := by
    show (match (tt_c M x r).state with
      | some q => _
      | none => 0) = _
    rw [hq]
  rw [tt_D_succ M x r q hq, hidx]
  exact tt_round_rsum _ _ (tt_D_inv M x r).1 t n hn1

/-- **The count hypothesis** [AB09, §1.7; the book's amortization]: in a run of `T` live
rounds, track `t`'s steps of scanned index above `i` number at most `T / 2^i + 1`.

**Proof sketch.** After such a step the levels `0, …, i` of track `t` are half full: its side
total below `i + 1` is `2^{i+1} − 1` (`tt_orbit_rsum`). Each later round changes it by at most
one, or resets it to `2^{i+1} − 1` after another such step; and such a step needs it to be `0`
or `2^{i+2} − 2`. So two such steps are at least `2^{i+1} − 1 ≥ 2^i` rounds apart, and
`tt_card_le_of_gap` counts them with the gap `2^i`. -/
private theorem tt_count (M : FinTM Bool) (x : List Bool) (T : ℕ)
    (hT : ∀ r < T, (tt_c M x r).state ≠ none) (t : Fin M.k) (i : ℕ) :
    ((Finset.range T).filter (fun s => i < tt_idxR M x t s)).card ≤ T / 2 ^ i + 1 := by
  set n := i + 1 with hn
  have hn1 : 1 ≤ n := Nat.le_add_left 1 i
  refine tt_card_le_of_gap T (2 ^ i) (Nat.two_pow_pos i) _
    (fun a ha => Finset.mem_range.mp (Finset.mem_filter.mp ha).1) fun a ha b hb hab => ?_
  obtain ⟨haT, hai⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbT, hbi⟩ := Finset.mem_filter.mp hb
  rw [Finset.mem_range] at haT hbT
  have F := fun r (hr : r < T) => tt_orbit_rsum M x r (hT r hr) t n hn1
  obtain ⟨hVa, hla⟩ := (F a haT).1 hai
  -- the levels below `n` stay laid out after round `a`
  have hlev : ∀ r, a + 1 ≤ r → r ≤ b → n ≤ (tt_D M x r).1 := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => exact fun _ => hla
    | succ r hr ih => exact fun hrb => (ih (by omega)).trans (F r (by omega)).2.2.2.1
  -- the side total drifts by at most one per round
  have hdrift : ∀ r, a + 1 ≤ r → r ≤ b →
      ((tt_rsum ((tt_D M x r).2 t) n : ℤ) - (2 ^ n - 1) ≤ r - (a + 1) ∧
        ((2 ^ n - 1 : ℤ) - tt_rsum ((tt_D M x r).2 t) n ≤ r - (a + 1))) := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      intro _
      rw [hVa]
      have := Nat.one_le_two_pow (n := n)
      push_cast [Nat.cast_sub this]
      constructor <;> omega
    | succ r hr ih =>
      intro hrb
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      by_cases hbig : n ≤ tt_idxR M x t r
      · rw [((F r (by omega)).1 hbig).1]
        have := Nat.one_le_two_pow (n := n)
        push_cast [Nat.cast_sub this]
        constructor <;> omega
      · obtain ⟨d₁, d₂⟩ := (F r (by omega)).2.2.1 (hlev r hr (by omega)) (by omega)
        push_cast
        constructor <;> omega
  obtain ⟨e₁, e₂⟩ := hdrift b (by omega) le_rfl
  have hb := (F b hbT).2.1 (hlev b (by omega) le_rfl) hbi
  have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have hpow : 2 ^ n = 2 * 2 ^ i := by rw [hn, pow_succ']
  rcases hb with hb | hb
  · rw [hb] at e₂
    push_cast at e₂
    have : (2 : ℤ) ^ n = 2 * 2 ^ i := by exact_mod_cast hpow
    have : (1 : ℤ) ≤ 2 ^ i := by exact_mod_cast Nat.one_le_two_pow
    have key : (a : ℤ) + 2 ^ i ≤ b := by omega
    exact_mod_cast key
  · rw [hb] at e₁
    have h4 : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
    push_cast [Nat.cast_sub h4] at e₁
    have : (2 : ℤ) ^ n = 2 * 2 ^ i := by exact_mod_cast hpow
    have : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
    have : (1 : ℤ) ≤ 2 ^ i := by exact_mod_cast Nat.one_le_two_pow
    have key : (a : ℤ) + 2 ^ i ≤ b := by omega
    exact_mod_cast key

/-- **The displacement invariant through a round** [AB09, §1.7]. If every track's whole side
total plus its head's displacement `pos t` is `2^{D.1} − 1`, and every displacement is at most
`r`, then after the round with action `a` the same holds with the displacements moved by the
heads' moves, and the level count `ℓ'` satisfies `2^{ℓ'} ≤ max (2^{D.1}) (2 (r + 1))`: an
extension at level `ℓ` needs every feeding zone empty, so a displacement of `2^ℓ − 1`.

**Proof sketch.** Induction over the round's tracks. A move changes its track's side total by
the opposite of its displacement (`tt_trackStep_rsum`, `tt_shift_dir`), and an extension adds
`2^ℓ` to every track's side total and to `2^ℓ − 1`. A short scan has an extreme side total
(`tt_rsum_low`: `0` or `2^{ℓ+1} − 2`), so `|pos t| = 2^ℓ − 1 ≤ r`. -/
private theorem tt_round_disp {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k)
    (hD : tt_fullD D) (pos : Fin k → ℤ) (r : ℕ)
    (hQ : ∀ t, (tt_rsum (D.2 t) D.1 : ℤ) + pos t = 2 ^ D.1 - 1) (hpos : ∀ t, |pos t| ≤ r) :
    (∀ t, (tt_rsum ((tt_roundData a D).2 t) (tt_roundData a D).1 : ℤ) +
      (pos t + (tt_moves a t : ℤ)) = 2 ^ (tt_roundData a D).1 - 1) ∧
    2 ^ (tt_roundData a D).1 ≤ max (2 ^ D.1) (2 * (r + 1)) := by
  set m := tt_moves a
  set H := tt_homeData a D
  have hHf : tt_fullD H := (tt_homeData_inv a D hD).1
  have key : ∀ j, (∀ t, (tt_rsum ((tt_Dtr m H j).2 t) (tt_Dtr m H j).1 : ℤ) + pos t +
      (if t.val < j then (m t : ℤ) else 0) = 2 ^ (tt_Dtr m H j).1 - 1) ∧
      2 ^ (tt_Dtr m H j).1 ≤ max (2 ^ D.1) (2 * (r + 1)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun t => ?_, le_max_left _ _⟩
      rw [if_neg (Nat.not_lt_zero _), add_zero]
      show (tt_rsum (zoneHomeWrite (D.2 t) _) D.1 : ℤ) + pos t = 2 ^ D.1 - 1
      rw [tt_rsum_homeWrite]
      exact hQ t
    | succ j ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      by_cases hj : j < k
      · rw [show tt_Dtr m H (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m H j)
          from dif_pos hj]
        set E := tt_Dtr m H j
        have hEf : tt_fullD E := (tt_Dtr_inv m H hHf j).1
        by_cases h0 : m ⟨j, hj⟩ = 0
        · rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ E = E from if_pos h0]
          refine ⟨fun t => ?_, ih₂⟩
          rw [← ih₁ t]
          by_cases ht : t = ⟨j, hj⟩
          · subst ht
            rw [if_pos (Nat.lt_succ_self j), if_neg (lt_irrefl j), h0]
            simp
          · have : t.val ≠ j := Fin.val_ne_of_ne ht
            by_cases htj : t.val < j
            · rw [if_pos htj, if_pos (by omega)]
            · rw [if_neg htj, if_neg (by omega)]
        · set dir := tt_dir (m ⟨j, hj⟩)
          rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ E = zoneTrackStepData dir ⟨j, hj⟩ E
            from if_neg h0]
          obtain ⟨-, -, c3, c4, c5⟩ := tt_trackStep_rsum dir ⟨j, hj⟩ E hEf
          have hsh : tt_shift dir = (m ⟨j, hj⟩ : ℤ) := tt_shift_dir _ h0
          have hℓ : (2 : ℤ) ^ (zoneTrackStepData dir ⟨j, hj⟩ E).1 = 2 ^ E.1 +
              (if zoneRebalanceIndex dir ⟨j, hj⟩ E < E.1 then 0 else 2 ^ E.1) := by
            rw [c5]
            split_ifs
            · ring
            · ring
          refine ⟨fun t => ?_, ?_⟩
          · by_cases ht : t = ⟨j, hj⟩
            · subst ht
              rw [c3, hℓ, if_pos (Nat.lt_succ_self j), ← hsh]
              have := ih₁ ⟨j, hj⟩
              rw [if_neg (lt_irrefl j), add_zero] at this
              linarith
            · have : t.val ≠ j := Fin.val_ne_of_ne ht
              obtain ⟨-, c4'⟩ := c4 t ht
              rw [c4', hℓ]
              have := ih₁ t
              have hif : (if t.val < j + 1 then (m t : ℤ) else 0) =
                  (if t.val < j then (m t : ℤ) else 0) := by
                by_cases htj : t.val < j
                · rw [if_pos htj, if_pos (by omega)]
                · rw [if_neg htj, if_neg (by omega)]
              rw [hif]
              push_cast
              linarith
          · rw [c5]
            split_ifs with hlt
            · exact ih₂
            · -- an extension at level `E.1`: the scanned side is extreme
              have hidx : zoneShiftIndex dir (E.2 ⟨j, hj⟩) = E.1 := by
                rw [← zoneRebalanceIndex_eq]
                exact eq_of_le_of_not_lt (zoneRebalanceIndex_le _ _ _) hlt
              have hl := tt_rsum_low dir (E.2 ⟨j, hj⟩) (hEf _) E.1 hidx.ge le_rfl
              have hq := ih₁ ⟨j, hj⟩
              rw [if_neg (lt_irrefl j), add_zero] at hq
              have hp := abs_le.mp (hpos ⟨j, hj⟩)
              have h2 : 2 ≤ 2 ^ (E.1 + 1) := Nat.le_self_pow (by omega) 2
              have hb : 2 ^ E.1 ≤ r + 1 := by
                cases hdir : dir
                · rw [hdir, if_neg (by simp)] at hl
                  rw [hl] at hq
                  push_cast [Nat.cast_sub h2] at hq
                  have : (2 : ℤ) ^ (E.1 + 1) = 2 * 2 ^ E.1 := pow_succ' 2 E.1
                  have : (2 : ℤ) ^ E.1 ≤ r + 1 := by linarith
                  exact_mod_cast this
                · rw [hdir, if_pos rfl] at hl
                  rw [hl] at hq
                  push_cast at hq
                  have : (2 : ℤ) ^ E.1 ≤ r + 1 := by linarith
                  exact_mod_cast this
              rw [pow_succ]
              exact le_max_of_le_right (by omega)
      · rw [show tt_Dtr m H (j + 1) = tt_Dtr m H j from dif_neg hj]
        refine ⟨fun t => ?_, ih₂⟩
        rw [← ih₁ t, if_pos (by omega), if_pos (by omega)]
  obtain ⟨k₁, k₂⟩ := key k
  refine ⟨fun t => ?_, k₂⟩
  have := k₁ t
  rw [if_pos t.isLt] at this
  rw [← add_assoc]
  exact this

/-- **The displacement invariant and the level bound along the run** [AB09, §1.7]: after `r`
steps every track's whole side total plus `M`'s head position is `2^{ℓ} − 1` for the level count
`ℓ`, and `2^ℓ ≤ 2 r + 1`.

**Proof sketch.** Induction on `r`: no level and heads at `0` at first; a live step is
`tt_round_disp` with the heads' moves (`Turing.Action.apply_workTapePos`) and `M`'s head bound
(`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`); a halted step changes nothing. -/
private theorem tt_D_level (M : FinTM Bool) (x : List Bool) (r : ℕ) :
    (∀ t, (tt_rsum ((tt_D M x r).2 t) (tt_D M x r).1 : ℤ) + (tt_c M x r).workTapePos t =
      2 ^ (tt_D M x r).1 - 1) ∧ 2 ^ (tt_D M x r).1 ≤ 2 * r + 1 := by
  induction r with
  | zero =>
    refine ⟨fun t => ?_, le_rfl⟩
    show (tt_rsum (ZoneContents.empty 0) 0 : ℤ) + (M.tm.runFrom (M.tm.initCfg x) 0).workTapePos t =
      2 ^ 0 - 1
    rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    rfl
  | succ r ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hc : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
    cases hq : (tt_c M x r).state with
    | none =>
      have hD : tt_D M x (r + 1) = tt_D M x r := by
        show (match (tt_c M x r).state with
          | some q => _
          | none => tt_D M x r) = _
        rw [hq]
      rw [hD, hc, MultiTapeTM.step_of_halt hq]
      exact ⟨ih₁, by omega⟩
    | some q =>
      obtain ⟨hact, -, -⟩ := tt_round_inv M (tt_c M x r) q hq _ (tt_D_inv M x r).1
        (tt_D_inv M x r).2
      have hpos : ∀ t, |(tt_c M x r).workTapePos t| ≤ r := fun t => by
        have h : (tt_c M x r).workTapePos t ∈ Finset.Icc ((M.tm.initCfg x).workTapePos t - r)
            ((M.tm.initCfg x).workTapePos t + r) :=
          MultiTapeTM.workTapePos_runFrom_mem_Icc M.tm (M.tm.initCfg x) r t
        rw [MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, Finset.mem_Icc] at h
        exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
      obtain ⟨d₁, d₂⟩ := tt_round_disp (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r))
        (tt_D M x r) (tt_D_inv M x r).1 _ r ih₁ hpos
      rw [tt_D_succ M x r q hq]
      refine ⟨fun t => ?_, d₂.trans (max_le (by omega) (by omega))⟩
      rw [hc, MultiTapeTM.step_of_some hq, Action.apply_workTapePos, ← hact]
      exact d₁ t

/-- **The level bound** [AB09, §1.7]: in a run of `T` live rounds every scanned index is at most
`log₂ T + 1`.

**Proof sketch.** The index of round `s` is at most the level count after it (`tt_orbit_rsum`),
whose power of two is at most `2 (s + 1) + 1 ≤ 2 T + 1 < 2^{log₂ T + 2}` (`tt_D_level`,
`Nat.lt_pow_succ_log_self`). -/
private theorem tt_idxR_le (M : FinTM Bool) (x : List Bool) (T : ℕ)
    (hT : ∀ r < T, (tt_c M x r).state ≠ none) (t : Fin M.k) :
    ∀ s < T, tt_idxR M x t s ≤ Nat.log 2 T + 1 := by
  intro s hs
  have h1 := (tt_orbit_rsum M x s (hT s hs) t 1 le_rfl).2.2.2.2
  have h2 := (tt_D_level M x (s + 1)).2
  have h3 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) T
  refine h1.trans ?_
  by_contra hc
  have h4 : 2 ^ (Nat.log 2 T + 2) ≤ 2 ^ (tt_D M x (s + 1)).1 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ] at h4
  omega

/-! ### The cost -/

/-- **The cost of a halting run** [AB09, §1.7]: if `M` is live for its first `t₀ ≥ 1` steps, the
zone machine's time `∑_{r < t₀ − 1} T_r + 1` is at most
`(2 + k (5 A + 1)) · (t₀ + 1)(log₂(t₀ + 1) + 1)`.

**Proof sketch.** The time is at most the sum of all `t₀` rounds' lengths (the last round takes
at least one step, `tt_T_ge`). Each round costs at most `2 + A ∑_t (2^{i₀} + 1) + k`
(`tt_τ_le`), so `Turing.sum_cost_le_of_count` applies with `B = 2`, the count hypothesis
`tt_count` and the level bound `L = log₂ t₀ + 1` (`tt_idxR_le`), giving
`2 t₀ + k (A ((L + 2) t₀ + 2^L) + t₀)`; then `2^L ≤ 2 t₀` (`Nat.pow_log_le_self`) and
`log₂ t₀ ≤ log₂ (t₀ + 1)` (`Nat.log_mono_right`). -/
private theorem tt_cost (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (t₀ : ℕ) (h1 : 1 ≤ t₀) (hl : ∀ r < t₀, (tt_c M x r).state ≠ none) :
    ∑ r ∈ Finset.range (t₀ - 1), tt_T M F x r + 1 ≤
      (2 + M.k * (5 * A + 1)) * ((t₀ + 1) * (Nat.log 2 (t₀ + 1) + 1)) := by
  set L := Nat.log 2 t₀ + 1 with hL
  -- the time is at most the sum of all the rounds
  have hsum : ∑ r ∈ Finset.range (t₀ - 1), tt_T M F x r + 1 ≤
      ∑ r ∈ Finset.range t₀, tt_T M F x r := by
    obtain ⟨s, rfl⟩ : ∃ s, t₀ = s + 1 := Nat.exists_eq_add_one.mpr h1
    rw [Nat.add_sub_cancel, Finset.sum_range_succ]
    have := tt_T_ge M F x s (hl s (by omega))
    omega
  -- each round's cost
  have hstep : ∀ s < t₀, tt_T M F x s ≤
      2 + A * ∑ t, (2 ^ tt_idxR M x t s + 1) + M.k := by
    intro s hs
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hl s hs)
    have hT : tt_T M F x s = 2 + ∑ j ∈ Finset.range M.k, tt_τ M F (x.map Sum.inl)
        (tt_moves (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)))
        (tt_homeData (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s))
        (moveInputPos (tt_ipOf M (tt_c M x s))
          (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).inputTape)
        ((tt_c M x s).output.map Sum.inl ++
          ((tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).output.map Sum.inl).toList) j := by
      show (match (tt_c M x s).state with
        | some q => _
        | none => 0) = _
      rw [hq]
    have hidx : ∀ t, tt_idxR M x t s =
        tt_idxA (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s) t := by
      intro t
      show (match (tt_c M x s).state with
        | some q => _
        | none => 0) = _
      rw [hq]
    rw [hT]
    have hle : ∀ j : Fin M.k, tt_τ M F (x.map Sum.inl)
        (tt_moves (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)))
        (tt_homeData (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s))
        (moveInputPos (tt_ipOf M (tt_c M x s))
          (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).inputTape)
        ((tt_c M x s).output.map Sum.inl ++
          ((tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).output.map Sum.inl).toList) j ≤
        A * (2 ^ tt_idxR M x j s + 1) + 1 := by
      intro j
      rw [hidx]
      exact tt_τ_le M F hk _ _ _ _ _ j.val j.isLt
    have hsumτ := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hle j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumτ
    simp only [Finset.sum_const, Finset.card_fin, Nat.nsmul_eq_mul, mul_one] at hsumτ
    rw [← Fin.sum_univ_eq_sum_range (fun j => tt_τ M F (x.map Sum.inl)
        (tt_moves (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)))
        (tt_homeData (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s))
        (moveInputPos (tt_ipOf M (tt_c M x s))
          (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).inputTape)
        ((tt_c M x s).output.map Sum.inl ++
          ((tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).output.map Sum.inl).toList) j) M.k]
    omega
  have hcost := sum_cost_le_of_count M.k t₀ L A 2 (fun t s => tt_idxR M x t s) (tt_T M F x)
    hstep (fun t => tt_idxR_le M x t₀ hl t) (fun t i _ => tt_count M x t₀ hl t i)
  -- the arithmetic
  have hpow : 2 ^ L ≤ 2 * t₀ := by
    rw [hL, pow_succ]
    have := Nat.pow_log_le_self 2 (show t₀ ≠ 0 by omega)
    omega
  have hlog : Nat.log 2 t₀ ≤ Nat.log 2 (t₀ + 1) := Nat.log_mono_right (Nat.le_succ t₀)
  set lg := Nat.log 2 (t₀ + 1)
  have hP : t₀ ≤ (t₀ + 1) * (lg + 1) := by nlinarith
  have hL3 : (L + 2) * t₀ ≤ 3 * ((t₀ + 1) * (lg + 1)) := by nlinarith
  refine hsum.trans (hcost.trans ?_)
  have e1 : 2 * t₀ ≤ 2 * ((t₀ + 1) * (lg + 1)) := by omega
  have e2 : M.k * (A * ((L + 2) * t₀ + 2 ^ L) + t₀) ≤
      M.k * (5 * A + 1) * ((t₀ + 1) * (lg + 1)) := by
    have : A * ((L + 2) * t₀ + 2 ^ L) + t₀ ≤ (5 * A + 1) * ((t₀ + 1) * (lg + 1)) := by
      nlinarith
    calc M.k * (A * ((L + 2) * t₀ + 2 ^ L) + t₀) ≤ M.k * ((5 * A + 1) * ((t₀ + 1) * (lg + 1))) :=
          Nat.mul_le_mul_left _ this
      _ = M.k * (5 * A + 1) * ((t₀ + 1) * (lg + 1)) := by ring
  nlinarith

/-! ### The target -/

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each side of a level is empty, half full or full, and the two sides
of a level together always hold the same number of cells. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, restoring
every level below `i` to half full, and a zone `i` is rebalanced at most once every `2^(i-1)`
simulated steps. Summing over the zones
`0, …, log₂ t + 1` that a run of `t` steps can rebalance gives `O(t log t)` steps in all. The
converse holds because `M'` writes an output symbol exactly when `M` does, in the same order, and
halts only when `M` halts. With no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  refine tt_route (fun M hk => ?_) M
  -- the track-step family, chosen once (`Turing.exists_zoneTrackStepTM`)
  obtain ⟨A, hA⟩ := exists_zoneTrackStepTM M.k
  choose S fin dec Mt entry X hnone hR using hA
  choose R hpre hspec using hR
  let F : tt_Fam M.k A := ⟨S, fin, dec, Mt, entry, X, hnone, R, hpre, hspec⟩
  refine ⟨tt_HS M F hk, rfl, 2 + M.k * (5 * A + 1), fun x o t h => ?_,
    fun x o' t' h => tt_converse M F hk x o' t' h⟩
  obtain ⟨t₀, ht₀, h1, hl, hHS⟩ := tt_forward_run M F hk x o t h
  refine hHS.mono ((tt_cost M F hk x t₀ h1 hl).trans (Nat.mul_le_mul_left _ ?_))
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩

end Turing.FinTM

## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesSealed.out =====



## ===== campaign/gates/102-g5-landing-fill/evidence/round2/seal/TwoTapesAxioms.out =====

'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_zero_tapes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_frame' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_route' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_LeafSt' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_decodeIn' does not depend on any axioms
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_homeRead' does not depend on any axioms
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_homeNew' does not depend on any axioms
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_moves' does not depend on any axioms
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_leafTr' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_leafTM' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_leafTM_tr_moves' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_leafTM_tr_workTapes_of_ne' depends on axioms: [propext,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_leaf_step' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Fam' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_dir' does not depend on any axioms
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_I' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Ph' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Mf' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_next' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_red' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_red_track_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_red_track_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_phFin' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_phDec' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_HS' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cfg' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cfg_mapState' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cfg_rowPre' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_mapState_eq_cfg' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_trackData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_idx' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_trackTime' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_next_ne' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_phase_seg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_track_seg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cfg0' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_act' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_homeData' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Dtr' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_stAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_τ' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_τ_of_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_tracks_seg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_τ_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_empty' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_homeWrite' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_pre_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_pre_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_rebalance_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_full_rebalance_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_shift' does not depend on any axioms
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_tape_rebalance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_fullD' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_trackStep_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_shift_dir' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Dtr_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_homeData_inv' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_roundData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rep' depends on axioms: [propext]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rep_home' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_round_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_c' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_D' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_D_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_D_inv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_moveInputPos_val' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_inputSymbol' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_ipOf' depends on axioms: [propext, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cs' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_T' depends on axioms: [propext, Classical.choice, Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cs_start' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cs_round' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cs_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cs_halt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_T_ge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_HS_init' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_forward_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_converse' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum_succ' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum_low' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum_rebalance_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum_rebalance_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum_homeWrite' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_rsum_extend' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_trackStep_rsum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Dtr_level_mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Dtr_other' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_idxA' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_Dtr_own' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_round_rsum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_card_le_of_gap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_idxR' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_orbit_rsum' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_count' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_round_disp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_D_level' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_idxR_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'_private.rvprobe.g102r2.TwoTapesAxioms.0.Turing.FinTM.tt_cost' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Turing.FinTM.two_work_tapes_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.two_work_tapes_binary' depends on axioms: [propext, Classical.choice, Quot.sound]

## ===== TCSlib/Complexity/TuringMachine/Robustness/TwoTapes.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction
import TCSlib.Complexity.TuringMachine.Build.ZoneRebalance
import TCSlib.Complexity.TuringMachine.Build.ZoneStep
import TCSlib.Complexity.TuringMachine.SymbolLift

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reduction to two work tapes

[HS66], as used in [AB09, §1.7] for the efficient universal machine: `k` work tapes are simulated
by two work tapes with a slowdown of `O(T log T)`. Run for run, every binary machine has a
binary two-work-tape equivalent that reproduces each halting run of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of the source.

## Deviations from [AB09] and [HS66]

* The slowdown is stated per run, with an existential constant, and padded with `+ 1` in both
  factors so that it covers the empty run (`t = 0`).
* The statement includes the converse (every completed output of the simulator is an output of
  the source), which the universal machine's correctness needs.
* The statement holds for every number of work tapes, zero and one included. With no work tapes
  there is nothing to fold: `M` runs on the two-tape host through the forwarding embedding
  `Turing.embedEmitTM`, beside two idle tapes.
* For `k ≥ 1` the simulator is built over the zone alphabet `Turing.ZoneSym k` (a binary symbol,
  or one cell holding a slot of every track), the formal counterpart of the book's alphabet of
  `k` parallel tracks with a buffer symbol, and is then made binary by the alphabet reduction
  `Turing.FinTM.alphabet_reduction_run` [AB09, Claim 1.5], which keeps the two work tapes and
  multiplies the time by a constant.

## Main definitions

No new definitions: the reduction is an existential contract.

## Main results

* `Turing.FinTM.two_work_tapes_run` — two work tapes suffice, with logarithmic overhead, run by
  run and with the converse [HS66].
* `Turing.FinTM.two_work_tapes_binary` — the same at the level of computed functions.

## Implementation notes

For `k ≥ 1` the simulator is a phase host (`Turing.phaseHostTM`) over `Turing.ZoneSym k` with two
work tapes: tape `0` carries `M`'s `k` work tapes as the tracks of one zoned tape
(`Turing.zonedTape`), every simulated head at the home cell, and tape `1` is scratch; the input
is read as `x.map Sum.inl`. One round simulates one step of `M`: a transition step reads the
home tuple and the input symbol, applies `M`'s transition, writes the new home symbols and emits
the encoded output; then each track runs one track step in the direction of its head move
(`Turing.exists_zoneTrackStepTM`: a rebalance at the scanned index, preceded by an extension of
the zones when the scan finds none), a stay taking no time. The rounds are chained as segments
(`Turing.Segment.iterate_seq`). Along the run every track represents the corresponding work tape
of `M` and is *full*: at each level `i` its two zones hold `2 · 2^i` cells together and the right
one holds `0`, `2^i` or `2 · 2^i`. The count of expensive steps uses side totals, the numbers of
cells in a track's right zones below a level: after a step of scanned index above `i` the levels
`0, …, i` are half full, so the next such step of the same track comes at least `2^i` rounds
later, and a zone `j ≥ 1` is rebalanced at most once every `2^(j-1)` steps, as in the sketch of
`Turing.FinTM.two_work_tapes_run`. An extension to level `ℓ` needs a head displacement of
`2^ℓ − 1`, so in a run of `T` live rounds every scanned index is at most `log₂ T + 1`, and
`Turing.sum_cost_le_of_count` sums the rounds' costs.

The file is long because it is one construction and its correctness proof: apart from a few
arithmetic facts, its lemmas are about the simulator's own definitions (its rounds, the
invariant along its run and its cost count), so a split would have to make these internals
public.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.7, the proof of Theorem 1.9.)
* [HS66] F. C. Hennie, R. E. Stearns, *Two-tape simulation of multitape Turing machines*,
  J. ACM 13(4), 1966, 533–546.
-/

namespace Turing.FinTM

/-! ### The frame and the zero-tape case -/

/-- **Zero work tapes** [HS66; AB09, §1.7]: a binary machine `M` without work tapes has a binary
equivalent with two work tapes that reproduces each halting run of `t` steps within
`1 · (t + 1)(log₂(t + 1) + 1)` steps, and whose completed outputs are outputs of `M`.

**Proof sketch.** Run `M` on the two-tape host through the forwarding embedding
`Turing.embedEmitTM` along the empty selection `Fin M.k ↪ Fin 2`, restarted at `M`'s initial
state. The host's initial configuration is the embedding of `M`'s into the blank frame with
heads at `0` and empty prefix (`Turing.embedEmitCfg_eq`, field by field from the `Cfg.init`
equations; the selected bank is empty). By `Turing.embedEmitTM_runFrom` the host's run is the
embedding of `M`'s run, so the two have the same state and the same output at every time
(`Turing.embedEmitCfg_state`, `Turing.embedEmitCfg_output`). Hence they halt together with the
same output, and `t ≤ (t + 1)(log₂(t + 1) + 1)` pads the time. -/
private theorem tt_zero_tapes (M : FinTM Bool) (hk : M.k = 0) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨σ⟩ : Nonempty (Fin M.k ↪ Fin 2) := ⟨Fin.castLEEmb (by omega)⟩
  -- the host: R1 of `M.tm`, restarted at `M`'s initial state
  obtain ⟨N, hq, hr⟩ : ∃ N : MultiTapeTM 2 Bool M.State,
      (∀ x, N.initCfg x = Cfg.init M.tm.q₀ x) ∧
        ∀ (x : List Bool) (c : Cfg 2 Bool M.State x) (t : ℕ),
          N.runFrom c t = (embedEmitTM σ M.tm).runFrom c t :=
    ⟨_, fun x => MultiTapeTM.initCfg_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ x,
      fun _ c t => MultiTapeTM.runFrom_with_q₀ (embedEmitTM σ M.tm) M.tm.q₀ c t⟩
  -- the host's initial configuration is the embedding of `M`'s into the blank frame
  have hinit : ∀ x : List Bool,
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.initCfg x) =
        Cfg.init M.tm.q₀ x := by
    intro x
    rw [MultiTapeTM.initCfg_eq]
    refine embedEmitCfg_eq σ _ _ [] _ _ ?_ ?_ ?_ ?_ ?_
    · simp only [Cfg.init_state]
    · simp only [Cfg.init_inputPos]
    · simp only [Cfg.init_output, List.append_nil]
    · intro i
      exact (i.cast hk).elim0
    · intro j _
      exact ⟨funext fun p => by simp only [Cfg.init_workTapes],
        by simp only [Cfg.init_workTapePos]⟩
  -- the host's run is the embedding of `M`'s
  have hrun : ∀ (x : List Bool) (t : ℕ), N.runFrom (N.initCfg x) t =
      embedEmitCfg σ (fun _ _ => none) (fun _ => 0) [] (M.tm.runFrom (M.tm.initCfg x) t) := by
    intro x t
    rw [hq, ← hinit x, hr, embedEmitTM_runFrom]
  refine ⟨{ k := 2, State := M.State, tm := N }, 1, rfl, fun x o t h => ?_, fun x o h => ?_⟩
  · obtain ⟨hs, ho⟩ := (computesInTime_iff M x o t).1 h
    have hb : t ≤ 1 * ((t + 1) * (Nat.log 2 (t + 1) + 1)) := by
      rw [Nat.one_mul]
      exact le_mul_of_le_of_one_le (Nat.le_succ t) (by omega)
    refine ComputesInTime.mono ?_ hb
    rw [computesInTime_iff]
    show (N.runFrom (N.initCfg x) t).state = none ∧ (N.runFrom (N.initCfg x) t).output = o
    refine ⟨?_, ?_⟩
    · rw [hrun, embedEmitCfg_state, hs]
    · rw [hrun, embedEmitCfg_output, ho, List.nil_append]
  · obtain ⟨t, ht⟩ := h
    obtain ⟨hs, ho⟩ := (computesInTime_iff _ x o t).1 ht
    have hs' : (N.runFrom (N.initCfg x) t).state = none := hs
    have ho' : (N.runFrom (N.initCfg x) t).output = o := ho
    rw [hrun, embedEmitCfg_state] at hs'
    rw [hrun, embedEmitCfg_output, List.nil_append] at ho'
    exact ⟨t, (computesInTime_iff M x o t).2 ⟨hs', ho'⟩⟩

/-- **The frame of the two-work-tape reduction** [HS66; AB09, §1.7, with Claim 1.5 for the
alphabet]: let `HS` be a machine over the zone alphabet `Turing.ZoneSym M.k` with two work tapes
that reproduces each halting run of `M` of `t` steps on the encoded input `x.map Sum.inl`, with
the encoded output, within `c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of
which on an encoded input is the encoding of an output of `M`. Then `M` has a binary equivalent
with two work tapes, with the same overhead up to a constant, and whose completed outputs are
outputs of `M`.

**Proof sketch.** Reduce `HS` to the binary alphabet by `Turing.FinTM.alphabet_reduction_run`
along `Sum.inl : Bool ↪ ZoneSym M.k`, which keeps the two work tapes and multiplies the time by a
constant `c₂`; the constant of the result is `c₂ · c₁`. Forward, `M`'s run gives `HS`'s within
`c₁ · (t + 1)(log₂(t + 1) + 1)` steps, and the reduction's forward direction gives the binary
machine's. Conversely, a completed output `w` of the binary machine comes from a completed output
`o'` of `HS` on the encoded input such that every binary word encoding to `o'` is `w`; the
converse property of `HS` writes `o'` as the encoding of an output `v` of `M`, so `v = w`. -/
private theorem tt_frame (M : FinTM Bool) (HS : FinTM (ZoneSym M.k)) (hHS : HS.k = 2) (c₁ : ℕ)
    (hfwd : ∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
      HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
        (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1))))
    (hconv : ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
      HS.ComputesInTime (x.map Sum.inl) o' t' →
        ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  obtain ⟨c₂, M', hk, hf, hc⟩ :=
    alphabet_reduction_run (Function.Embedding.inl : Bool ↪ ZoneSym M.k) HS
  have hinl : ⇑(Function.Embedding.inl : Bool ↪ ZoneSym M.k) = Sum.inl :=
    funext fun b => Function.Embedding.inl_apply b
  rw [hinl] at hf hc
  refine ⟨M', c₂ * c₁, hk.trans hHS, fun x o t h => ?_, fun x o h => ?_⟩
  · rw [Nat.mul_assoc]
    exact hf x o _ (hfwd x o t h)
  · obtain ⟨t', o', ht', hv⟩ := hc x o h
    obtain ⟨t, v, hM, rfl⟩ := hconv x o' t' ht'
    obtain rfl := hv v rfl
    exact ⟨t, hM⟩

/-- **The route of the two-work-tape reduction** [HS66; AB09, §1.7]: if every binary machine
with at least one work tape has a two-work-tape zone machine with the forward property and the
image converse of `tt_frame`, then every binary machine has a binary equivalent with two work
tapes, with overhead `O((t + 1) log(t + 1))` per run of `t` steps, whose completed outputs are
outputs of the source.

**Proof sketch.** Without work tapes, `tt_zero_tapes`; otherwise the hypothesis gives the zone
machine, and `tt_frame` finishes. -/
private theorem tt_route
    (hHS : ∀ M : FinTM Bool, 1 ≤ M.k →
      ∃ (HS : FinTM (ZoneSym M.k)) (_ : HS.k = 2) (c₁ : ℕ),
        (∀ (x o : List Bool) (t : ℕ), M.ComputesInTime x o t →
          HS.ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
            (c₁ * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
        ∀ (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ),
          HS.ComputesInTime (x.map Sum.inl) o' t' →
            ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl)
    (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  by_cases hk : M.k = 0
  · exact tt_zero_tapes M hk
  · obtain ⟨HS, hHSk, c₁, hf, hc⟩ := hHS M (by omega)
    exact tt_frame M HS hHSk c₁ hf hc

/-! ### The leaf: one simulated transition on the home cell -/

/-- The states of the transition step of the two-work-tape simulation of `M` [HS66; AB09,
§1.7]: `Sum.inl q`, about to simulate one transition of `M` at state `q`, and `Sum.inr (q', m)`,
the transition done, with `M`'s successor state `q'` and the head moves `m` still pending. -/
private abbrev tt_LeafSt (M : FinTM Bool) : Type :=
  M.State ⊕ (M.State × (Fin M.k → SignType))

/-- The input symbol of the binary source read through the zone alphabet's embedding
`Sum.inl` (a cell that holds no binary symbol reads as blank). -/
private def tt_decodeIn {k : ℕ} : Option (ZoneSym k) → Option Bool
  | some (.inl b) => some b
  | _ => none

/-- The home tuple read from the home cell of the zoned tape (`Turing.zonedTape`): track `t`
reads the virtual symbol stored in its slot, a blank or unoccupied slot reading as blank. -/
private def tt_homeRead {k : ℕ} (w : Option (ZoneSym k)) (t : Fin k) : Option Bool :=
  (zoneCellOfCell w t).join

/-- The value track `t` holds after one transition of `M` with action `a` from the home
tuple `v`: the written symbol, or the old one when nothing is written. -/
private def tt_homeNew {k : ℕ} {S : Type} (a : Action k Bool S) (v : Fin k → Option Bool)
    (t : Fin k) : Option Bool :=
  (a.workTapes t).1.getD (v t)

/-- The head moves of one transition of `M` with action `a`. -/
private def tt_moves {k : ℕ} {S : Type} (a : Action k Bool S) (t : Fin k) : SignType :=
  (a.workTapes t).2

/-- **The transition step's table** [HS66; AB09, §1.7]. No public row applies a finite-state
transition to the home cell of the zoned tape and the input head in one step, so the
simulation writes this one leaf. At `Sum.inl q` it reads the home tuple from the home cell of
tape `0` (`tt_homeRead`) and the input symbol through `Sum.inl` (`tt_decodeIn`), applies `M`'s
transition at `q`, writes the new home tuple, moves the input head as `M` does, emits `M`'s
output symbol through `Sum.inl`, keeps both work heads, and goes to `Sum.inr (q', m)` with `M`'s
successor state and head moves, or halts when `M` halts. A state `Sum.inr _` halts (it is
redirected by the host and never runs). -/
private def tt_leafTr (M : FinTM Bool) (s : tt_LeafSt M) (inp : Option (ZoneSym M.k))
    (w : Fin 2 → Option (ZoneSym M.k)) : Action 2 (ZoneSym M.k) (tt_LeafSt M) :=
  match s with
  | .inl q =>
    { inputTape := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).inputTape
      workTapes := fun j => if j = 0 then
          (some (some (.inr fun t =>
            some (tt_homeNew (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0)))
              (tt_homeRead (w 0)) t))), 0)
        else (none, 0)
      output := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).output.map Sum.inl
      state := (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0))).state.map fun q' =>
        .inr (q', tt_moves (M.tm.tr q (tt_decodeIn inp) (tt_homeRead (w 0)))) }
  | .inr _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The transition step** [HS66; AB09, §1.7]: the two-tape machine over `Turing.ZoneSym M.k`
whose table is `tt_leafTr`. -/
private def tt_leafTM (M : FinTM Bool) : MultiTapeTM 2 (ZoneSym M.k) (tt_LeafSt M) where
  q₀ := .inl M.tm.q₀
  tr := tt_leafTr M

/-- The transition step keeps every work head. -/
private theorem tt_leafTM_tr_moves (M : FinTM Bool) (s : tt_LeafSt M) (inp : Option (ZoneSym M.k))
    (w : Fin 2 → Option (ZoneSym M.k)) (j : Fin 2) :
    (((tt_leafTM M).tr s inp w).workTapes j).2 = 0 := by
  rcases s with q | _
  · show (if j = 0 then _ else ((none : Option (Option (ZoneSym M.k))), (0 : SignType))).2 = 0
    split_ifs <;> rfl
  · rfl

/-- The transition step writes nothing on tape `1`. -/
private theorem tt_leafTM_tr_workTapes_of_ne (M : FinTM Bool) (q : M.State)
    (inp : Option (ZoneSym M.k)) (w : Fin 2 → Option (ZoneSym M.k)) {j : Fin 2} (hj : j ≠ 0) :
    ((tt_leafTM M).tr (.inl q) inp w).workTapes j = (none, 0) :=
  if_neg hj

/-- **One transition step** [HS66; AB09, §1.7]: from a configuration at `Sum.inl q`, one step
of the transition machine applies `M`'s transition `a` at `q` to the home tuple read from the
home cell and to the decoded input symbol. It writes the new home tuple into the cell under
head `0` and leaves tape `1`, moves the input head by `a`'s input move, keeps both work heads,
appends `a`'s output symbol through `Sum.inl`, and goes to `Sum.inr (q', m)` for `a`'s
successor `q'` and head moves `m`, or halts with `a`.

**Proof sketch.** `Turing.MultiTapeTM.step_of_some` applies the table's action; its fields are
read through `Turing.Action.apply_state`, `_inputPos`, `_workTapePos`, `_output` and
`Turing.Action.apply_workTapes`, the table being this file's own definition. -/
private theorem tt_leaf_step (M : FinTM Bool) {x : List (ZoneSym M.k)}
    (c : Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x) (q : M.State) (hc : c.state = some (.inl q)) :
    (tt_leafTM M).step c =
      { state := (M.tm.tr q (tt_decodeIn c.inputSymbol)
            (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).state.map fun q' =>
          .inr (q', tt_moves (M.tm.tr q (tt_decodeIn c.inputSymbol)
            (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))))
        inputPos := moveInputPos c.inputPos (M.tm.tr q (tt_decodeIn c.inputSymbol)
          (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).inputTape
        workTapes := fun j => if j = 0 then
            Function.update (c.workTapes 0) (c.workTapePos 0) (some (.inr fun t =>
              some (tt_homeNew (M.tm.tr q (tt_decodeIn c.inputSymbol)
                (tt_homeRead (c.workTapes 0 (c.workTapePos 0))))
                (tt_homeRead (c.workTapes 0 (c.workTapePos 0))) t)))
          else c.workTapes j
        workTapePos := c.workTapePos
        output := c.output ++ ((M.tm.tr q (tt_decodeIn c.inputSymbol)
          (tt_homeRead (c.workTapes 0 (c.workTapePos 0)))).output.map Sum.inl).toList } := by
  have hW : c.workTapeSymbols = fun i => c.workTapes i (c.workTapePos i) :=
    funext (Cfg.workTapeSymbols_eq c)
  rw [MultiTapeTM.step_of_some hc]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · rw [Action.apply_state, hW]
    rfl
  · rw [Action.apply_inputPos, hW]
    rfl
  · funext j p
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq, hW]
    by_cases hj : j = 0
    · subst hj
      rfl
    · rw [tt_leafTM_tr_workTapes_of_ne M q _ _ hj, Option.getD_none, Function.update_eq_self]
      show c.workTapes j p = (if j = 0 then _ else c.workTapes j) p
      rw [if_neg hj]
  · funext j
    rw [Action.apply_workTapePos, tt_leafTM_tr_moves, SignType.coe_zero, add_zero]
  · rw [Action.apply_output, hW]
    rfl

/-! ### The controller: the phase host over the transition step and the track steps -/

/-- **A track-step family** for `k` tracks with constant `A` [AB09, §1.7]: per direction `dir`
(`true` for a right move) and track `t`, a two-tape machine over `Turing.ZoneSym k` with finite
states, an entry, live exits, and per input a `Turing.Contract` with precondition
`Turing.zoneRowPre`, time at most `A · (2^{i₀} + 1)` for the scanned index `i₀`, and an endpoint
at the data `Turing.zoneTrackStepData dir t D` with the scratch head, the input head and the
output kept. `Turing.exists_zoneTrackStepTM` gives one. -/
private structure tt_Fam (k A : ℕ) where
  /-- the state types -/
  S : Bool → Fin k → Type
  /-- their finiteness -/
  fin : ∀ dir t, Fintype (S dir t)
  /-- their decidable equality -/
  dec : ∀ dir t, DecidableEq (S dir t)
  /-- the machines -/
  M : ∀ dir t, MultiTapeTM 2 (ZoneSym k) (S dir t)
  /-- the entries -/
  entry : ∀ dir t, S dir t
  /-- the exits -/
  X : ∀ dir t, Set (Option (S dir t))
  /-- the exits are live -/
  none_nmem : ∀ dir t, none ∉ X dir t
  /-- the contracts -/
  R : ∀ dir t (x : List (ZoneSym k)), Contract (M dir t) (entry dir t) (X dir t) (ZoneData k) x
  /-- their precondition -/
  pre : ∀ dir t x, (R dir t x).pre = zoneRowPre
  /-- their time and endpoint -/
  spec : ∀ dir t x (D : ZoneData k) (d : Cfg 2 (ZoneSym k) (S dir t) x),
    d.state = some (entry dir t) → zoneRowPre D d →
      (R dir t x).time D d ≤ A * (2 ^ zoneRebalanceIndex dir t D + 1) ∧
      zoneRowPre (zoneTrackStepData dir t D) ((R dir t x).post D d) ∧
      ((R dir t x).post D d).workTapePos 1 = d.workTapePos 1 ∧
      ((R dir t x).post D d).inputPos = d.inputPos ∧ ((R dir t x).post D d).output = d.output

/-- The direction of a head move: `true` for a right move, `false` otherwise. -/
private def tt_dir : SignType → Bool
  | .pos => true
  | _ => false

/-- The phase index of the simulation: `none` for the transition step, `some (q', m, t)` for
the step of track `t` in the round whose transition went to `q'` with head moves `m`. -/
private abbrev tt_I (M : FinTM Bool) : Type :=
  Option (M.State × (Fin M.k → SignType) × Fin M.k)

/-- The phases' state types: the transition step's, and per track the track step's of its
direction. -/
private def tt_Ph (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) : tt_I M → Type
  | none => tt_LeafSt M
  | some (_, m, t) => F.S (tt_dir (m t)) t

/-- The phases' machines: the transition step, and per track the track step of its
direction (for a stay, it is entered and left at once). -/
private def tt_Mf (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → MultiTapeTM 2 (ZoneSym M.k) (tt_Ph M F i)
  | none => tt_leafTM M
  | some (_, m, t) => F.M (tt_dir (m t)) t

/-- The state after the step of track `t`: the next track's entry, or the transition step at
`q'` after the last track. -/
private def tt_next (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (t : Fin M.k) : Σ i, tt_Ph M F i :=
  if h : t.val + 1 < M.k then
    ⟨some (q', m, ⟨t.val + 1, h⟩), F.entry (tt_dir (m ⟨t.val + 1, h⟩)) ⟨t.val + 1, h⟩⟩
  else ⟨none, .inl q'⟩

open Classical in
/-- **The redirects** of the simulation's phase host: the transition step's exit
`Sum.inr (q', m)` goes to track `0`'s entry; a track's exit (for a stay, its entry) goes to
`tt_next`; nothing else is redirected. -/
private noncomputable def tt_red (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k) :
    (i : tt_I M) → tt_Ph M F i → Option (Σ i, tt_Ph M F i)
  | none, .inl _ => none
  | none, .inr (q', m) => some ⟨some (q', m, ⟨0, hk⟩), F.entry (tt_dir (m ⟨0, hk⟩)) ⟨0, hk⟩⟩
  | some (q', m, t), s =>
    if (m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨ (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)
    then some (tt_next M F q' m t) else none

open Classical in
/-- A track's exit (for a stay, its entry) is redirected to `tt_next`. -/
private theorem tt_red_track_pos (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k) (s : F.S (tt_dir (m t)) t)
    (h : (m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨ (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)) :
    tt_red M F hk (some (q', m, t)) s = some (tt_next M F q' m t) :=
  if_pos h

open Classical in
/-- Every other state of a track's phase is not redirected. -/
private theorem tt_red_track_neg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k) (s : F.S (tt_dir (m t)) t)
    (h : ¬((m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨
      (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t))) :
    tt_red M F hk (some (q', m, t)) s = none :=
  if_neg h

/-- The phases' state types are finite. -/
private def tt_phFin (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → Fintype (tt_Ph M F i)
  | none => inferInstanceAs (Fintype (tt_LeafSt M))
  | some (_, m, t) => F.fin (tt_dir (m t)) t

/-- The phases' state types have decidable equality. -/
private def tt_phDec (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) :
    (i : tt_I M) → DecidableEq (tt_Ph M F i)
  | none => inferInstanceAs (DecidableEq (tt_LeafSt M))
  | some (_, m, t) => F.dec (tt_dir (m t)) t

/-- **The two-work-tape zone machine** [HS66; AB09, §1.7]: the phase host
`Turing.phaseHostTM` over the transition step and the track steps of `F`, started at the
transition step at `M`'s initial state. Tape `0` is the zoned tape, tape `1` the scratch
tape. -/
private noncomputable def tt_HS (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k) :
    FinTM (ZoneSym M.k) :=
  letI := tt_phFin M F
  letI := tt_phDec M F
  { k := 2
    State := Σ i, tt_Ph M F i
    tm := phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) }

/-! ### The configurations at the round boundaries -/

/-- **A configuration at a phase boundary**: state `s`, input head at `ip`, output `out`, tape
`0` the zoned tape of `D` with its head at home, tape `1` blank with its head at `0`. -/
private def tt_cfg {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S) (D : ZoneData k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) : Cfg 2 (ZoneSym k) S x :=
  ⟨s, ip, fun j => if j = 0 then zonedTape D.2 else fun _ => none, fun _ => 0, out⟩

/-- Renaming the state of a phase-boundary configuration renames its state only. -/
private theorem tt_cfg_mapState {k : ℕ} {S S' : Type} {x : List (ZoneSym k)} (s : Option S)
    (D : ZoneData k) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) (f : S → S') :
    (tt_cfg s D ip out).mapState f = (tt_cfg (s.map f) D ip out : Cfg 2 (ZoneSym k) S' x) :=
  Cfg.mapState_eq_of_fields _ f _ rfl rfl rfl rfl rfl

/-- A phase-boundary configuration satisfies the zone rows' precondition. -/
private theorem tt_cfg_rowPre {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S)
    (D : ZoneData k) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) :
    zoneRowPre D (tt_cfg s D ip out : Cfg 2 (ZoneSym k) S x) :=
  (zoneRowPre_iff D _).mpr ⟨rfl, rfl, fun _ => rfl⟩

/-- **A row endpoint is a phase-boundary configuration**: a configuration that satisfies the
zone rows' precondition at `D`, with head `1` at `0`, input head `ip` and output `out`, is
`tt_cfg` at `D` once its state is renamed to the constant `s`, if it is live.

**Proof sketch.** Field by field (`Turing.Cfg.mapState_eq_of_fields`): the state is `some s`
since `d` is live; tape `0` and head `0` are the precondition's (`Turing.zoneRowPre_iff`), tape `1`
is blank by it, head `1` is `h1`, and the input head and the output are the hypotheses. -/
private theorem tt_mapState_eq_cfg {k : ℕ} {S S' : Type} {x : List (ZoneSym k)}
    (D : ZoneData k) (d : Cfg 2 (ZoneSym k) S x) (hp : zoneRowPre D d) (s : S')
    (hs : d.state.isSome) (h1 : d.workTapePos 1 = 0) (ip : Fin (x.length + 2))
    (hi : d.inputPos = ip) (out : List (ZoneSym k)) (ho : d.output = out) :
    d.mapState (fun _ => s) = tt_cfg (some s) D ip out := by
  obtain ⟨h0, hp0, hb⟩ := (zoneRowPre_iff D d).mp hp
  obtain ⟨s₀, hs₀⟩ := Option.isSome_iff_exists.mp hs
  refine Cfg.mapState_eq_of_fields d _ _ ?_ hi ?_ ?_ ho
  · rw [hs₀]
    rfl
  · funext j p
    by_cases hj : j = 0
    · subst hj
      rw [h0]
      rfl
    · obtain rfl := Fin.eq_one_of_ne_zero j hj
      rw [hb p]
      rfl
  · funext j
    by_cases hj : j = 0
    · subst hj
      rw [hp0]
      rfl
    · obtain rfl := Fin.eq_one_of_ne_zero j hj
      rw [h1]
      rfl

/-! ### One track's phase -/

/-- The data after track `t`'s step for head move `s`: unchanged for a stay, otherwise
`Turing.zoneTrackStepData` in the move's direction. -/
private def tt_trackData {k : ℕ} (s : SignType) (t : Fin k) (D : ZoneData k) : ZoneData k :=
  if s = 0 then D else zoneTrackStepData (tt_dir s) t D

/-- The scanned index of track `t`'s step for head move `s`: `0` for a stay. -/
private def tt_idx {k : ℕ} (s : SignType) (t : Fin k) (D : ZoneData k) : ℕ :=
  if s = 0 then 0 else zoneRebalanceIndex (tt_dir s) t D

/-- The time of track `t`'s phase before its dispatch step: `0` for a stay, otherwise the
track step's contract time from the phase-boundary configuration. -/
private def tt_trackTime (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (t : Fin M.k) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) : ℕ :=
  if m t = 0 then 0 else
    (F.R (tt_dir (m t)) t x).time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)

/-- The step of track `t` leaves its phase: `tt_next` is at another phase. -/
private theorem tt_next_ne (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (t : Fin M.k) : (tt_next M F q' m t).1 ≠ some (q', m, t) := by
  unfold tt_next
  split_ifs <;> simp [Fin.ext_iff]

/-- **A track's contract inside the host** [HS66; AB09, §1.7]: a contract for track `t`'s phase
from its entry, whose exits are live and are exactly the states that `tt_red` redirects, gives a
live run of the zone machine from the phase-boundary configuration at that entry, one dispatch
step past the contract's time, to the phase-boundary configuration at `tt_next` with data `D'`,
if the contract's endpoint satisfies the rows' precondition at `D'` and keeps head `1`, the input
head and the output.

**Proof sketch.** The redirect table meets the hypotheses of the phase host's contract form
`Turing.Contract.inPhase` (`tt_red_track_pos`, `tt_red_track_neg`), every target at another
phase (`tt_next_ne`). Its run (`Turing.Contract.inPhase_time`) and its liveness
(`Turing.Contract.live`) give the segment; its exit is the target `tt_next`, and its endpoint is
the contract's with that state (`Turing.Contract.inPhase_post`), the phase-boundary configuration
there (`tt_mapState_eq_cfg`). -/
private theorem tt_phase_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k)
    {X : Set (Option (tt_Ph M F (some (q', m, t))))}
    (C : Contract (tt_Mf M F (some (q', m, t))) (F.entry (tt_dir (m t)) t) X (ZoneData M.k) x)
    (hnone : none ∉ X)
    (hX : ∀ s, some s ∈ X ↔ ((m t = 0 ∧ s = F.entry (tt_dir (m t)) t) ∨
      (m t ≠ 0 ∧ some s ∈ F.X (tt_dir (m t)) t)))
    (D D' : ZoneData M.k) (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k))
    (hpre : C.pre D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out))
    (hpost : zoneRowPre D' (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)))
    (h1 : (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)).workTapePos 1 = 0)
    (hin : (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)).inputPos = ip)
    (hout : (C.post D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out)).output = out) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True)
      (tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out)
      (tt_cfg (some (tt_next M F q' m t)) D' ip out)
      (C.time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out) + 1) := by
  set c : Cfg 2 (ZoneSym M.k) (tt_Ph M F (some (q', m, t))) x :=
    tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out
  set d : Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) x :=
    tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out
  have hdc : d.mapState (fun _ => F.entry (tt_dir (m t)) t) = c := tt_cfg_mapState _ _ _ _ _
  have hred : ∀ s, some s ∉ X → tt_red M F hk (some (q', m, t)) s = none :=
    fun s hs => tt_red_track_neg M F hk q' m t s fun h => hs ((hX s).mpr h)
  have hsome : ∀ s, some s ∈ X →
      ∃ q, tt_red M F hk (some (q', m, t)) s = some q ∧ q.1 ≠ some (q', m, t) :=
    fun s hs => ⟨_, tt_red_track_pos M F hk q' m t s ((hX s).mp hs), tt_next_ne M F q' m t⟩
  set C' := Contract.inPhase (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) (some (q', m, t))
    C hnone hred hsome with hC'
  have hs : d.state = some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩ := rfl
  have hp : C'.pre D d := by
    rw [hC', Contract.inPhase_pre, hdc]
    exact hpre
  have hT : C'.time D d = C.time D c + 1 := by
    rw [hC', Contract.inPhase_time, hdc]
  have hP : C'.post D d = (C.post D c).bindState (tt_red M F hk (some (q', m, t))) := by
    rw [hC', Contract.inPhase_post, hdc]
  obtain ⟨s, hsX, hst⟩ := C'.exit_mem D d hs hp
  rw [tt_red_track_pos M F hk q' m t s ((hX s).mp hsX), hP, Cfg.bindState_state] at hst
  obtain ⟨s', hs', -⟩ := Option.bind_eq_some_iff.mp hst
  have hE : C'.post D d = tt_cfg (some (tt_next M F q' m t)) D' ip out := by
    rw [← tt_mapState_eq_cfg D' (C.post D c) hpost (tt_next M F q' m t) (by rw [hs']; rfl) h1 ip
      hin out hout, hP]
    refine (Cfg.mapState_eq_of_fields _ _ _ ?_ (by rw [Cfg.bindState_inputPos])
      (by funext j p; rw [Cfg.bindState_workTapes]) (by funext j; rw [Cfg.bindState_workTapePos])
      (by rw [Cfg.bindState_output])).symm
    rw [Cfg.bindState_state, hst, hs']
    rfl
  refine (segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩
  · rw [← hT, ← hE]
    exact C'.run D d hs hp
  · rw [Set.mem_singleton_iff]
    exact C'.live D d hs hp (hT ▸ hu)

/-- **One track's phase** [HS66; AB09, §1.7]: from the entry of track `t`'s phase, at a
phase-boundary configuration with data `D`, the zone machine runs live for the phase's time
plus one dispatch step to the phase-boundary configuration at `tt_next` with the data after
track `t`'s step, the input head and the output kept; the phase's time is at most
`A · (2^{i₀} + 1)` for its scanned index `i₀`.

**Proof sketch.** By `tt_phase_seg`, with the zero-time contract (`Turing.Contract.zero`) for a
stay, whose only exit is the entry, and the track step's contract for a move, whose specification
gives the endpoint and the time bound. -/
private theorem tt_track_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (t : Fin M.k)
    (D : ZoneData M.k) (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True)
        (tt_cfg (some ⟨some (q', m, t), F.entry (tt_dir (m t)) t⟩) D ip out)
        (tt_cfg (some (tt_next M F q' m t)) (tt_trackData (m t) t D) ip out)
        (tt_trackTime M F x m t D ip out + 1) ∧
      tt_trackTime M F x m t D ip out ≤ A * (2 ^ tt_idx (m t) t D + 1) := by
  by_cases h0 : m t = 0
  · -- a stay: the zero-time contract, redirected at once
    have hT : tt_trackTime M F x m t D ip out = 0 := if_pos h0
    have hD : tt_trackData (m t) t D = D := if_pos h0
    rw [hT, hD]
    refine ⟨?_, Nat.zero_le _⟩
    have H := tt_phase_seg M F hk q' m t
      (Contract.zero (tt_Mf M F (some (q', m, t))) (F.entry (tt_dir (m t)) t) (ZoneData M.k) x)
      (fun h => Option.noConfusion (Set.mem_singleton_iff.mp h))
      (fun s => ⟨fun h => Or.inl ⟨h0, Option.some.inj (Set.mem_singleton_iff.mp h)⟩,
        fun h => h.elim (fun h' => by rw [h'.2]; exact Set.mem_singleton _)
          (fun h' => absurd h0 h'.1)⟩)
      D D ip out (by rw [Contract.zero_pre]; trivial)
      (by rw [Contract.zero_post]; exact tt_cfg_rowPre _ D ip out)
      (by rw [Contract.zero_post]; rfl) (by rw [Contract.zero_post]; rfl)
      (by rw [Contract.zero_post]; rfl)
    rwa [Contract.zero_time] at H
  · -- a move: the track step's contract
    obtain ⟨htime, hpost, h1, hin, hout⟩ := F.spec (tt_dir (m t)) t x D
      (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out) rfl (tt_cfg_rowPre _ D ip out)
    have hT : tt_trackTime M F x m t D ip out =
        (F.R (tt_dir (m t)) t x).time D (tt_cfg (some (F.entry (tt_dir (m t)) t)) D ip out) :=
      if_neg h0
    have hD : tt_trackData (m t) t D = zoneTrackStepData (tt_dir (m t)) t D := if_neg h0
    have hI : tt_idx (m t) t D = zoneRebalanceIndex (tt_dir (m t)) t D := if_neg h0
    rw [hT, hD, hI]
    refine ⟨tt_phase_seg M F hk q' m t (F.R (tt_dir (m t)) t x) (F.none_nmem _ _)
      (fun s => ⟨fun h => Or.inr ⟨h0, h⟩, fun h => h.elim (fun h' => absurd h'.1 h0) And.right⟩)
      D _ ip out (by rw [F.pre]; exact tt_cfg_rowPre _ D ip out) hpost h1 hin hout, htime⟩

/-! ### One round: the transition step, then every track -/

/-- **A round's start configuration** at the transition step: tape `0` is the zoned tape of `D`
except at the home cell, which holds `h0`; the rest as in `tt_cfg`. The first round starts with
a blank home cell, every later one with the zoned tape's own. -/
private def tt_cfg0 {k : ℕ} {S : Type} {x : List (ZoneSym k)} (s : Option S) (D : ZoneData k)
    (h0 : Option (ZoneSym k)) (ip : Fin (x.length + 2)) (out : List (ZoneSym k)) :
    Cfg 2 (ZoneSym k) S x :=
  ⟨s, ip, fun j => if j = 0 then Function.update (zonedTape D.2) 0 h0 else fun _ => none,
    fun _ => 0, out⟩

/-- The transition of `M` at `q` on input symbol `inp` from the homes of `D`. -/
private def tt_act (M : FinTM Bool) (q : M.State) (inp : Option Bool) (D : ZoneData M.k) :
    Action M.k Bool M.State :=
  M.tm.tr q inp fun t => (D.2 t).home

/-- The data after the home write of action `a`. -/
private def tt_homeData {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) :
    ZoneData k :=
  ⟨D.1, fun t => zoneHomeWrite (D.2 t) (tt_homeNew a (fun t => (D.2 t).home) t)⟩

/-- The data after the steps of the tracks below `j`, for head moves `m`, from `D`. -/
private def tt_Dtr {k : ℕ} (m : Fin k → SignType) (D : ZoneData k) : ℕ → ZoneData k
  | 0 => D
  | j + 1 => if h : j < k then tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m D j) else tt_Dtr m D j

/-- The state at the start of track `j`'s phase, or the transition step at `q'` after the
last track. -/
private def tt_stAt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (q' : M.State)
    (m : Fin M.k → SignType) (j : ℕ) : Σ i, tt_Ph M F i :=
  if h : j < M.k then ⟨some (q', m, ⟨j, h⟩), F.entry (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩⟩
  else ⟨none, .inl q'⟩

/-- The time of track `j`'s phase in a round, with its dispatch step. -/
private def tt_τ (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (j : ℕ) : ℕ :=
  if h : j < M.k then tt_trackTime M F x m ⟨j, h⟩ (tt_Dtr m D j) ip out + 1 else 0

/-- Below the track count, a track's phase time in a round is its phase's time plus the dispatch
step. -/
private theorem tt_τ_of_lt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List (ZoneSym M.k))
    (m : Fin M.k → SignType) (D : ZoneData M.k) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (j : ℕ) (hj : j < M.k) :
    tt_τ M F x m D ip out j = tt_trackTime M F x m ⟨j, hj⟩ (tt_Dtr m D j) ip out + 1 :=
  dif_pos hj

/-- **The tracks of a round** [HS66; AB09, §1.7]: from track `0`'s entry, the zone machine runs
live through every track's phase in order, to the transition step at `q'` with the data after
every track's step, in `∑ j < k` of the phases' times.

**Proof sketch.** `Turing.Segment.iterate_seq` over the tracks, each track by `tt_track_seg`;
consecutive boundaries match because `tt_next` at track `j` is `tt_stAt` at `j + 1`. -/
private theorem tt_tracks_seg (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q' : M.State) (m : Fin M.k → SignType) (D : ZoneData M.k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cfg (some (tt_stAt M F q' m 0)) D ip out)
      (tt_cfg (some ⟨none, .inl q'⟩) (tt_Dtr m D M.k) ip out)
      (∑ j ∈ Finset.range M.k, tt_τ M F x m D ip out j) := by
  have hend : tt_stAt M F q' m M.k = ⟨none, .inl q'⟩ := dif_neg (lt_irrefl _)
  have H := Segment.iterate_seq
    (M := phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) (F := {none})
    (P := fun _ => True)
    (fun j => (tt_cfg (some (tt_stAt M F q' m j)) (tt_Dtr m D j) ip out :
      Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) x))
    (tt_τ M F x m D ip out) trivial M.k (fun j hj => ?_)
  · dsimp only at H
    rw [hend] at H
    exact H
  · have hs : tt_stAt M F q' m j = ⟨some (q', m, ⟨j, hj⟩), F.entry (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩⟩ :=
      dif_pos hj
    have hn : tt_next M F q' m ⟨j, hj⟩ = tt_stAt M F q' m (j + 1) := rfl
    have hD : tt_Dtr m D (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) := dif_pos hj
    have hτ := tt_τ_of_lt M F x m D ip out j hj
    show Segment _ _ _ (tt_cfg (some (tt_stAt M F q' m j)) (tt_Dtr m D j) ip out)
      (tt_cfg (some (tt_stAt M F q' m (j + 1))) (tt_Dtr m D (j + 1)) ip out) _
    rw [hs, hD, hτ, ← hn]
    exact (tt_track_seg M F hk q' m ⟨j, hj⟩ (tt_Dtr m D j) ip out).1

/-- **One round** [HS66; AB09, §1.7]. From the transition step at `q`, with data `D` whose
homes are what the home cell `h0` reads and with decoded input symbol `inp`, let `a` be `M`'s
transition at `q` on `inp` and the homes of `D`. If `a` halts, the zone machine halts after one
step with `a`'s output symbol appended. Otherwise, with successor `q'`, it runs live to the
transition step at `q'`, with the data after the home write and every track's step, the input
head moved by `a` and `a`'s output symbol appended, in `2 + ∑ j < k` of the tracks' phase times.

**Proof sketch.** One transition step (`tt_leaf_step`) writes the home tuple: the home cell
becomes the zoned tape's of the written data (`Turing.zonedTape_homeWrite`). In the host it is
the tagged phase run (`Turing.phaseHostTM_run_le`, for a halt) or, with the redirect of its
exit, two steps to track `0`'s entry (`Turing.phaseHostTM_run`); the tracks follow
(`tt_tracks_seg`) and the two segments concatenate (`Turing.Segment.trans`). -/
private theorem tt_round (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    {x : List (ZoneSym M.k)} (q : M.State) (D : ZoneData M.k) (h0 : Option (ZoneSym M.k))
    (hread : ∀ t, tt_homeRead h0 t = (D.2 t).home) (ip : Fin (x.length + 2))
    (out : List (ZoneSym M.k)) (inp : Option Bool)
    (hinp : tt_decodeIn (tt_cfg0 (some (.inl q)) D h0 ip out :
      Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).inputSymbol = inp) :
    ((tt_act M q inp D).state = none →
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
          ((tt_cfg0 (some (.inl q)) D h0 ip out :
            Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none)) 1).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
          ((tt_cfg0 (some (.inl q)) D h0 ip out :
            Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none)) 1).output =
        out ++ ((tt_act M q inp D).output.map Sum.inl).toList) ∧
    ∀ q', (tt_act M q inp D).state = some q' →
      Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True)
        ((tt_cfg0 (some (.inl q)) D h0 ip out :
          Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x).mapState (Sigma.mk none))
        (tt_cfg (some ⟨none, .inl q'⟩)
          (tt_Dtr (tt_moves (tt_act M q inp D)) (tt_homeData (tt_act M q inp D) D) M.k)
          (moveInputPos ip (tt_act M q inp D).inputTape)
          (out ++ ((tt_act M q inp D).output.map Sum.inl).toList))
        (2 + ∑ j ∈ Finset.range M.k, tt_τ M F x (tt_moves (tt_act M q inp D))
          (tt_homeData (tt_act M q inp D) D) (moveInputPos ip (tt_act M q inp D).inputTape)
          (out ++ ((tt_act M q inp D).output.map Sum.inl).toList) j) := by
  set c₀ : Cfg 2 (ZoneSym M.k) (tt_LeafSt M) x := tt_cfg0 (some (.inl q)) D h0 ip out with hc₀
  set a := tt_act M q inp D with ha
  have hr : c₀.workTapes 0 (c₀.workTapePos 0) = h0 := by
    show Function.update (zonedTape D.2) 0 h0 0 = h0
    exact Function.update_self _ _ _
  have hR : tt_homeRead h0 = fun t => (D.2 t).home := funext hread
  have hstep := tt_leaf_step M c₀ q rfl
  rw [hr, hR, hinp] at hstep
  change (tt_leafTM M).step c₀ =
    { state := a.state.map fun q' => .inr (q', tt_moves a)
      inputPos := moveInputPos c₀.inputPos a.inputTape
      workTapes := fun j => if j = 0 then
          Function.update (c₀.workTapes 0) (c₀.workTapePos 0)
            (some (.inr fun t => some (tt_homeNew a (fun t => (D.2 t).home) t)))
        else c₀.workTapes j
      workTapePos := c₀.workTapePos
      output := c₀.output ++ (a.output.map Sum.inl).toList } at hstep
  have h₀ : (tt_Mf M F none).runFrom c₀ 0 = c₀ := MultiTapeTM.runFrom_zero
  have h1 : (tt_Mf M F none).runFrom c₀ 1 = (tt_leafTM M).step c₀ :=
    MultiTapeTM.runFrom_succ_eq_step.trans MultiTapeTM.runFrom_zero
  have hguard : ∀ u < 1, ∀ s, ((tt_Mf M F none).runFrom c₀ u).state = some s →
      tt_red M F hk none s = none := by
    intro u hu s hs
    rw [Nat.lt_one_iff.mp hu, h₀] at hs
    obtain rfl : (Sum.inl q : tt_LeafSt M) = s := Option.some.inj hs
    rfl
  refine ⟨fun hn => ?_, fun q' hq' => ?_⟩
  · have H := phaseHostTM_run_le (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) none c₀ 1
      hguard 1 le_rfl
    rw [H, h1, hstep]
    refine ⟨?_, ?_⟩
    · rw [Cfg.mapState_state]
      show Option.map _ (a.state.map _) = none
      rw [hn]
      rfl
    · rw [Cfg.mapState_output]
      rfl
  · have hs₁ : ((tt_leafTM M).step c₀).state = some (.inr (q', tt_moves a)) := by
      rw [hstep]
      show a.state.map _ = _
      rw [hq']
      rfl
    have hred : tt_red M F hk none (.inr (q', tt_moves a)) =
        some (tt_stAt M F q' (tt_moves a) 0) := by
      show some _ = some _
      rw [show tt_stAt M F q' (tt_moves a) 0 = _ from dif_pos hk]
    have H := phaseHostTM_run (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk) none c₀ _ 1 h1
      _ hs₁ _ hred hguard
    have hend : ((tt_leafTM M).step c₀).mapState (fun _ => tt_stAt M F q' (tt_moves a) 0) =
        tt_cfg (some (tt_stAt M F q' (tt_moves a) 0)) (tt_homeData a D)
          (moveInputPos ip a.inputTape) (out ++ (a.output.map Sum.inl).toList) := by
      refine Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_
      · rw [hs₁]
        rfl
      · rw [hstep]
        rfl
      · rw [hstep]
        funext j p
        by_cases hj : j = 0
        · subst hj
          show Function.update (Function.update (zonedTape D.2) 0 h0) 0 _ p = zonedTape _ p
          rw [Function.update_idem, zonedTape_homeWrite]
          rfl
        · show (if j = 0 then _ else c₀.workTapes j) p = (if j = 0 then _ else fun _ => none) p
          rw [if_neg hj, if_neg hj]
          show (if j = 0 then _ else fun _ => none) p = none
          rw [if_neg hj]
      · rw [hstep]
        rfl
      · rw [hstep]
        rfl
    have hlead : Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
        (fun _ => True) (c₀.mapState (Sigma.mk none))
        (tt_cfg (some (tt_stAt M F q' (tt_moves a) 0)) (tt_homeData a D)
          (moveInputPos ip a.inputTape) (out ++ (a.output.map Sum.inl).toList)) 2 := by
      refine (segment_iff _ _ _ _ _ _).mpr ⟨?_, fun u hu => ?_, fun _ _ => trivial⟩
      · exact H.2.trans hend
      · rw [H.1 u (by omega), Set.mem_singleton_iff, Cfg.mapState_state]
        rcases Nat.lt_or_ge u 1 with h | h
        · rw [Nat.lt_one_iff.mp h, h₀]
          exact fun h => by cases h
        · obtain rfl : u = 1 := by omega
          rw [h1, hs₁]
          exact fun h => by cases h
    exact hlead.trans (tt_tracks_seg M F hk q' (tt_moves a) (tt_homeData a D) _ _)

/-- **The time bound of a round's track phases** [AB09, §1.7]: track `j`'s phase, with its
dispatch, takes at most `A · (2^{i₀} + 1) + 1` steps for its scanned index `i₀` (`0` for a
stay). -/
private theorem tt_τ_le (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List (ZoneSym M.k)) (m : Fin M.k → SignType) (D : ZoneData M.k)
    (ip : Fin (x.length + 2)) (out : List (ZoneSym M.k)) (j : ℕ) (hj : j < M.k) :
    tt_τ M F x m D ip out j ≤ A * (2 ^ tt_idx (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) + 1) + 1 := by
  rw [tt_τ_of_lt M F x m D ip out j hj, Nat.add_le_add_iff_right]
  exact (tt_track_seg M F hk (x := x) M.tm.q₀ m ⟨j, hj⟩ (tt_Dtr m D j) ip out).2

/-! ### Fullness: the classical zone discipline -/

/-- **Fullness** of one track's contents [AB09, §1.7]: at every laid-out level `i` the two zones
together hold exactly `zoneCapacity i = 2 · 2^i` cells, and the right one holds `0`, `2^i` or
`2 · 2^i` (so the left one holds the complement: each side is empty, half full or full). -/
private def tt_full {ℓ : ℕ} (z : ZoneContents ℓ) : Prop :=
  ∀ i : Fin ℓ, (z.left i).length + (z.right i).length = zoneCapacity i.val ∧
    ((z.right i).length = 0 ∨ (z.right i).length = 2 ^ i.val ∨
      (z.right i).length = zoneCapacity i.val)

/-- The empty contents at level `0` are full (there is no level). -/
private theorem tt_full_empty : tt_full (ZoneContents.empty 0) :=
  fun i => i.elim0

/-- The home write keeps fullness: it changes no zone. -/
private theorem tt_full_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool)
    (hz : tt_full z) : tt_full (zoneHomeWrite z v) := by
  intro i
  rw [zoneHomeWrite_left, zoneHomeWrite_right]
  exact hz i

/-- **The extension keeps fullness**: the old levels are kept and the new one is half full on
both sides (`Turing.ZoneContents.extend_words_castSucc`, `_last`). -/
private theorem tt_full_extend {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z) :
    tt_full z.extend := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have hl := ZoneContents.extend_words_last false z
    have hr := ZoneContents.extend_words_last true z
    rw [ZoneContents.words_false] at hl
    rw [ZoneContents.words_true] at hr
    rw [hl, hr, List.length_replicate, Fin.val_last, zoneCapacity_eq]
    exact ⟨by ring, Or.inr (Or.inl rfl)⟩
  · have hl := ZoneContents.extend_words_castSucc false z i
    have hr := ZoneContents.extend_words_castSucc true z i
    rw [ZoneContents.words_false, ZoneContents.words_false] at hl
    rw [ZoneContents.words_true, ZoneContents.words_true] at hr
    rw [hl, hr, Fin.coe_castSucc]
    exact hz i

/-- **Fullness gives the classical state of a right move** [AB09, §1.7]: below the scanned
index `j` the right zones are empty and the left ones full, the right zone `j` holds at least
`2^j` cells, and the left zone `j` has room for `2^j` cells (the hypotheses of
`Turing.zoneCascadeRight_lengths`).

**Proof sketch.** The right zones below `j` are empty (`Turing.zoneShiftIndex_empty`), so by
fullness the left ones hold the whole capacity; the right zone `j` is nonempty
(`Turing.zoneShiftIndex_nonempty`), so by fullness it holds `2^j` or `2 · 2^j` cells, and the
left zone `j` the rest of the capacity `2 · 2^j`. -/
private theorem tt_full_pre_true {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z) {j : ℕ}
    (hj : zoneShiftIndex true z = j) (h : j < ℓ) :
    (∀ k (hk : k < j), z.right ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j), (z.left ⟨k, by omega⟩).length = zoneCapacity k) ∧
    2 ^ j ≤ (z.right ⟨j, h⟩).length ∧ (z.left ⟨j, h⟩).length + 2 ^ j ≤ zoneCapacity j := by
  subst hj
  have hr (k : ℕ) (hk : k < zoneShiftIndex true z) : z.right ⟨k, by omega⟩ = [] := by
    have := zoneShiftIndex_empty true z ⟨k, by omega⟩ hk
    rwa [ZoneContents.words_true] at this
  have hne := zoneShiftIndex_nonempty true z h
  rw [ZoneContents.words_true] at hne
  have hpos : 0 < (z.right ⟨_, h⟩).length := List.length_pos_iff.mpr hne
  obtain ⟨hsum, hcase⟩ := hz ⟨_, h⟩
  have hc := zoneCapacity_eq (zoneShiftIndex true z)
  have hsum' : (z.left ⟨_, h⟩).length + (z.right ⟨_, h⟩).length =
      zoneCapacity (zoneShiftIndex true z) := hsum
  have hcase' : (z.right ⟨_, h⟩).length = 0 ∨
      (z.right ⟨_, h⟩).length = 2 ^ zoneShiftIndex true z ∨
      (z.right ⟨_, h⟩).length = zoneCapacity (zoneShiftIndex true z) := hcase
  have hdonor : 2 ^ zoneShiftIndex true z ≤ (z.right ⟨_, h⟩).length := by
    rcases hcase' with h0 | h0 | h0 <;> omega
  refine ⟨hr, fun k hk => ?_, hdonor, by omega⟩
  have := (hz ⟨k, by omega⟩).1
  rwa [hr k hk, List.length_nil, add_zero] at this

/-- **Fullness gives the classical state of a left move**: the mirror of `tt_full_pre_true`, the
hypotheses of `Turing.zoneCascadeLeft_lengths`.

**Proof sketch.** As for `tt_full_pre_true`, with the left stack feeding: the left zones below
the index are empty, so the right ones are full, and the left donor holds at least `2^j` cells,
so the right zone at the index has room for `2^j`. -/
private theorem tt_full_pre_false {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z) {j : ℕ}
    (hj : zoneShiftIndex false z = j) (h : j < ℓ) :
    (∀ k (hk : k < j), z.left ⟨k, by omega⟩ = []) ∧
    (∀ k (hk : k < j), (z.right ⟨k, by omega⟩).length = zoneCapacity k) ∧
    2 ^ j ≤ (z.left ⟨j, h⟩).length ∧ (z.right ⟨j, h⟩).length + 2 ^ j ≤ zoneCapacity j := by
  subst hj
  have hl (k : ℕ) (hk : k < zoneShiftIndex false z) : z.left ⟨k, by omega⟩ = [] := by
    have := zoneShiftIndex_empty false z ⟨k, by omega⟩ hk
    rwa [ZoneContents.words_false] at this
  have hne := zoneShiftIndex_nonempty false z h
  rw [ZoneContents.words_false] at hne
  have hpos : 0 < (z.left ⟨_, h⟩).length := List.length_pos_iff.mpr hne
  obtain ⟨hsum, hcase⟩ := hz ⟨_, h⟩
  have hc := zoneCapacity_eq (zoneShiftIndex false z)
  have hsum' : (z.left ⟨_, h⟩).length + (z.right ⟨_, h⟩).length =
      zoneCapacity (zoneShiftIndex false z) := hsum
  have hcase' : (z.right ⟨_, h⟩).length = 0 ∨
      (z.right ⟨_, h⟩).length = 2 ^ zoneShiftIndex false z ∨
      (z.right ⟨_, h⟩).length = zoneCapacity (zoneShiftIndex false z) := hcase
  have hdonor : 2 ^ zoneShiftIndex false z ≤ (z.left ⟨_, h⟩).length := by
    rcases hcase' with h0 | h0 | h0 <;> omega
  refine ⟨hl, fun k hk => ?_, hdonor, by omega⟩
  have := (hz ⟨k, by omega⟩).1
  rwa [hl k hk, List.length_nil, zero_add] at this

/-- **A right rebalance keeps fullness, and halves the levels below its index** [AB09, §1.7]:
under fullness, with a nonempty feeding zone at the scanned index `j`, the rebalanced contents
are full, every level below `j` is half full on both sides, and the levels above `j` are kept.

**Proof sketch.** Fullness and the scan give the classical pre-state of
`Turing.zoneCascadeRight_lengths` (`tt_full_pre_true`): right zones below `j` empty, left ones
full, a right donor of `2^j` or `2 · 2^j` cells and room for `2^j` on the left at `j`. The
cascade's lengths are then `2^k` on both sides below `j`, and at `j` the right side loses `2^j`
cells to the left; above `j` nothing changes (`Turing.zoneRebalance_frame`). -/
private theorem tt_full_rebalance_true {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex true z < ℓ) :
    tt_full (zoneRebalance true z) ∧
      ∀ i : Fin ℓ, i.val < zoneShiftIndex true z →
        ((zoneRebalance true z).left i).length = 2 ^ i.val ∧
          ((zoneRebalance true z).right i).length = 2 ^ i.val := by
  set j := zoneShiftIndex true z with hj
  obtain ⟨hr, hl, hdonor, hroom⟩ := tt_full_pre_true z hz hj.symm h
  obtain ⟨hsum, hcase⟩ := hz ⟨j, h⟩
  have hc : zoneCapacity j = 2 * 2 ^ j := zoneCapacity_eq j
  have hsum' : (z.left ⟨j, h⟩).length + (z.right ⟨j, h⟩).length = zoneCapacity j := hsum
  have hcase' : (z.right ⟨j, h⟩).length = 0 ∨ (z.right ⟨j, h⟩).length = 2 ^ j ∨
      (z.right ⟨j, h⟩).length = zoneCapacity j := hcase
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame true z k hk
  rw [zoneRebalance_of_lt true z h, zoneCascade_true] at hframe ⊢
  obtain ⟨hlow, hjr, hjl⟩ := zoneCascadeRight_lengths j h z hr hl hdonor hroom
  refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ hij => ?_⟩
  · rcases lt_trichotomy i j with hij | rfl | hij
    · obtain ⟨h1, h2⟩ := hlow i hij
      refine ⟨?_, Or.inr (Or.inl h1)⟩
      rw [h1, h2, zoneCapacity_eq]
      ring
    · refine ⟨?_, ?_⟩
      · show ((zoneCascadeRight _ z).left ⟨_, h⟩).length +
          ((zoneCascadeRight _ z).right ⟨_, h⟩).length = zoneCapacity _
        rw [hjr, hjl]
        omega
      · show ((zoneCascadeRight _ z).right ⟨_, h⟩).length = 0 ∨
          ((zoneCascadeRight _ z).right ⟨_, h⟩).length = 2 ^ _ ∨
          ((zoneCascadeRight _ z).right ⟨_, h⟩).length = zoneCapacity _
        rw [hjr]
        rcases hcase' with h0 | h0 | h0
        · omega
        · left
          show (z.right ⟨j, h⟩).length - 2 ^ j = 0
          omega
        · right; left
          show (z.right ⟨j, h⟩).length - 2 ^ j = 2 ^ j
          have : (z.right ⟨j, h⟩).length = 2 * 2 ^ j := h0.trans hc
          omega
    · obtain ⟨hfl, hfr⟩ := hframe ⟨i, hi⟩ hij
      rw [hfl, hfr]
      exact hz ⟨i, hi⟩
  · obtain ⟨h1, h2⟩ := hlow i hij
    exact ⟨h2, h1⟩

/-- **A left rebalance keeps fullness, and halves the levels below its index**: the mirror of
`tt_full_rebalance_true`.

**Proof sketch.** As for `tt_full_rebalance_true`, with the left stack feeding:
`Turing.zoneCascadeLeft_lengths` under the mirrored classical pre-state (`tt_full_pre_false`:
left zones below the index empty, so right ones full; the left donor holds `2^j` or `2 · 2^j`
cells), and `Turing.zoneRebalance_frame` above the index. -/
private theorem tt_full_rebalance_false {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex false z < ℓ) :
    tt_full (zoneRebalance false z) ∧
      ∀ i : Fin ℓ, i.val < zoneShiftIndex false z →
        ((zoneRebalance false z).left i).length = 2 ^ i.val ∧
          ((zoneRebalance false z).right i).length = 2 ^ i.val := by
  set j := zoneShiftIndex false z with hj
  obtain ⟨hl, hr, hdonor, hroom⟩ := tt_full_pre_false z hz hj.symm h
  obtain ⟨hsum, hcase⟩ := hz ⟨j, h⟩
  have hc : zoneCapacity j = 2 * 2 ^ j := zoneCapacity_eq j
  have hsum' : (z.left ⟨j, h⟩).length + (z.right ⟨j, h⟩).length = zoneCapacity j := hsum
  have hcase' : (z.right ⟨j, h⟩).length = 0 ∨ (z.right ⟨j, h⟩).length = 2 ^ j ∨
      (z.right ⟨j, h⟩).length = zoneCapacity j := hcase
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame false z k hk
  rw [zoneRebalance_of_lt false z h, zoneCascade_false] at hframe ⊢
  obtain ⟨hlow, hjl, hjr⟩ := zoneCascadeLeft_lengths j h z hl hr hdonor hroom
  refine ⟨fun ⟨i, hi⟩ => ?_, fun ⟨i, hi⟩ hij => hlow i hij⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · obtain ⟨h1, h2⟩ := hlow i hij
    refine ⟨?_, Or.inr (Or.inl h2)⟩
    rw [h1, h2, zoneCapacity_eq]
    ring
  · refine ⟨?_, ?_⟩
    · show ((zoneCascadeLeft _ z).left ⟨_, h⟩).length +
        ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = zoneCapacity _
      rw [hjr, hjl]
      omega
    · show ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = 0 ∨
        ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = 2 ^ _ ∨
        ((zoneCascadeLeft _ z).right ⟨_, h⟩).length = zoneCapacity _
      rw [hjr]
      rcases hcase' with h0 | h0 | h0
      · right; left
        show (z.right ⟨j, h⟩).length + 2 ^ j = 2 ^ j
        omega
      · right; right
        show (z.right ⟨j, h⟩).length + 2 ^ j = zoneCapacity j
        omega
      · omega
  · obtain ⟨hfl, hfr⟩ := hframe ⟨i, hi⟩ hij
    rw [hfl, hfr]
    exact hz ⟨i, hi⟩

/-- The signed displacement of a head move in direction `dir`. -/
private def tt_shift : Bool → ℤ
  | true => 1
  | false => -1

/-- **A rebalance moves the represented tape** under fullness [AB09, §1.7]: the tape the
rebalanced track represents is the old one read one cell further in the move's direction. -/
private theorem tt_tape_rebalance {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex dir z < ℓ) (p : ℤ) :
    zoneTrackTape (zoneRebalance dir z) p = zoneTrackTape z (p + tt_shift dir) := by
  have hpow : ∀ j : ℕ, 2 ^ (j - 1) ≤ 2 ^ j := fun j => Nat.pow_le_pow_right (by norm_num) (by omega)
  cases dir
  · obtain ⟨-, hr, -, hroom⟩ := tt_full_pre_false z hz rfl h
    rw [zoneTrackTape_rebalance_left z h hr (le_trans (Nat.add_le_add_left (hpow _) _) hroom)]
    rfl
  · obtain ⟨-, hl, -, hroom⟩ := tt_full_pre_true z hz rfl h
    rw [zoneTrackTape_rebalance_right z h hl (le_trans (Nat.add_le_add_left (hpow _) _) hroom)]
    rfl

/-- **Fullness of the data**: every track's contents are full (`tt_full`). -/
private def tt_fullD {k : ℕ} (D : ZoneData k) : Prop :=
  ∀ t, tt_full (D.2 t)

/-- **One track's step keeps the data full and moves that track's represented tape**
[HS66; AB09, §1.7]: under fullness, after `Turing.zoneTrackStepData dir t D` the data are full,
track `t` represents its old tape read one cell further in direction `dir`, and every other
track represents its old tape.

**Proof sketch.** With a nonempty feeding zone the step is the rebalance of track `t`
(`Turing.zoneTrackStepData_of_lt`, `Turing.zoneRebalanceData_eq`): `tt_full_rebalance_true`/
`_false` and `tt_tape_rebalance` on track `t`, `Function.update_of_ne` elsewhere. Otherwise it
extends every track and then rebalances (`Turing.zoneTrackStepData_of_not_lt`,
`Turing.zoneExtendData_eq`): the extension keeps fullness (`tt_full_extend`) and every
represented tape (`Turing.zoneTrackTape_extend`), and the retried scan is below the new level
count (`Turing.zoneRebalanceIndex_extend_of_short`). -/
private theorem tt_trackStep_inv {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k)
    (hD : tt_fullD D) :
    tt_fullD (zoneTrackStepData dir t D) ∧
      ∀ t' p, zoneTrackTape ((zoneTrackStepData dir t D).2 t') p =
        zoneTrackTape (D.2 t') (if t' = t then p + tt_shift dir else p) := by
  have hreb : ∀ (E : ZoneData k), tt_fullD E → zoneRebalanceIndex dir t E < E.1 →
      tt_fullD (zoneRebalanceData dir t E) ∧
        ∀ t' p, zoneTrackTape ((zoneRebalanceData dir t E).2 t') p =
          zoneTrackTape (E.2 t') (if t' = t then p + tt_shift dir else p) := by
    intro E hE hlt
    rw [zoneRebalanceIndex_eq] at hlt
    rw [zoneRebalanceData_eq]
    refine ⟨fun t' => ?_, fun t' p => ?_⟩
    · show tt_full (Function.update E.2 t (zoneRebalance dir (E.2 t)) t')
      by_cases ht : t' = t
      · subst ht
        rw [Function.update_self]
        cases dir
        · exact (tt_full_rebalance_false _ (hE _) hlt).1
        · exact (tt_full_rebalance_true _ (hE _) hlt).1
      · rw [Function.update_of_ne ht]
        exact hE t'
    · show zoneTrackTape (Function.update E.2 t (zoneRebalance dir (E.2 t)) t') p = _
      by_cases ht : t' = t
      · subst ht
        rw [Function.update_self, if_pos rfl]
        exact tt_tape_rebalance dir _ (hE _) hlt p
      · rw [Function.update_of_ne ht, if_neg ht]
  by_cases hlt : zoneRebalanceIndex dir t D < D.1
  · rw [zoneTrackStepData_of_lt dir t hlt]
    exact hreb D hD hlt
  · rw [zoneTrackStepData_of_not_lt dir t hlt]
    have hidx := zoneRebalanceIndex_extend_of_short dir t D hlt
    have hE : tt_fullD (zoneExtendData D) := by
      rw [zoneExtendData_eq]
      exact fun t' => tt_full_extend _ (hD t')
    have hlt' : zoneRebalanceIndex dir t (zoneExtendData D) < (zoneExtendData D).1 := by
      rw [hidx, zoneExtendData_eq]
      exact Nat.lt_succ_self _
    obtain ⟨hf, htape⟩ := hreb _ hE hlt'
    refine ⟨hf, fun t' p => ?_⟩
    rw [htape]
    rw [zoneExtendData_eq]
    exact congrFun (zoneTrackTape_extend _) _

/-! ### The invariant: the represented tapes -/

/-- A nonzero head move's direction has the move's displacement. -/
private theorem tt_shift_dir (s : SignType) (hs : s ≠ 0) : tt_shift (tt_dir s) = (s : ℤ) := by
  cases s
  · exact absurd rfl hs
  · rfl
  · rfl

/-- **The tracks of a round keep fullness and move the represented tapes** [HS66; AB09,
§1.7]: after the steps of the tracks below `j` with head moves `m`, the data are full and every
track `t` below `j` represents its old tape shifted by `m t`, every other track its old tape.

**Proof sketch.** Induction on `j`, over the tracks of one round: a stay changes nothing, and a
move is `tt_trackStep_inv` with `tt_shift_dir`. -/
private theorem tt_Dtr_inv {k : ℕ} (m : Fin k → SignType) (D : ZoneData k) (hD : tt_fullD D)
    (j : ℕ) :
    tt_fullD (tt_Dtr m D j) ∧ ∀ t p, zoneTrackTape ((tt_Dtr m D j).2 t) p =
      zoneTrackTape (D.2 t) (if t.val < j then p + (m t : ℤ) else p) := by
  induction j with
  | zero =>
    exact ⟨hD, fun t p => by rw [if_neg (Nat.not_lt_zero _)]; rfl⟩
  | succ j ih =>
    obtain ⟨hf, htape⟩ := ih
    by_cases hj : j < k
    · have hDj : tt_Dtr m D (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) := dif_pos hj
      rw [hDj]
      by_cases h0 : m ⟨j, hj⟩ = 0
      · rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) = tt_Dtr m D j from if_pos h0]
        refine ⟨hf, fun t p => ?_⟩
        rw [htape]
        by_cases ht : t = ⟨j, hj⟩
        · subst ht
          rw [if_neg (lt_irrefl j), if_pos (Nat.lt_succ_self j), h0, SignType.coe_zero, add_zero]
        · have : t.val ≠ j := Fin.val_ne_of_ne ht
          by_cases htj : t.val < j
          · rw [if_pos htj, if_pos (by omega)]
          · rw [if_neg htj, if_neg (by omega)]
      · rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m D j) =
          zoneTrackStepData (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩ (tt_Dtr m D j) from if_neg h0]
        obtain ⟨hf', htape'⟩ := tt_trackStep_inv (tt_dir (m ⟨j, hj⟩)) ⟨j, hj⟩ _ hf
        refine ⟨hf', fun t p => ?_⟩
        rw [htape', htape]
        by_cases ht : t = ⟨j, hj⟩
        · subst ht
          rw [if_pos rfl, if_neg (lt_irrefl j), if_pos (Nat.lt_succ_self j),
            tt_shift_dir _ h0]
        · have : t.val ≠ j := Fin.val_ne_of_ne ht
          rw [if_neg ht]
          by_cases htj : t.val < j
          · rw [if_pos htj, if_pos (by omega)]
          · rw [if_neg htj, if_neg (by omega)]
    · have hDj : tt_Dtr m D (j + 1) = tt_Dtr m D j := dif_neg hj
      rw [hDj]
      refine ⟨hf, fun t p => ?_⟩
      rw [htape, if_pos (by omega), if_pos (by omega)]

/-- **The home write keeps fullness and writes the represented tapes at the head** [AB09,
§1.7]: after `tt_homeData a D`, track `t` represents its old tape with the new home value at
position `0`. -/
private theorem tt_homeData_inv {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k)
    (hD : tt_fullD D) :
    tt_fullD (tt_homeData a D) ∧ ∀ t p, zoneTrackTape ((tt_homeData a D).2 t) p =
      if p = 0 then tt_homeNew a (fun t => (D.2 t).home) t else zoneTrackTape (D.2 t) p :=
  ⟨fun t => tt_full_homeWrite _ _ (hD t), fun _ p => zoneTrackTape_homeWrite _ _ p⟩

/-- The data after a whole round, from `D`, for `M`'s action `a`. -/
private def tt_roundData {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) :
    ZoneData k :=
  tt_Dtr (tt_moves a) (tt_homeData a D) k

/-- **The represented tapes** of data `D` are the work tapes of `M`'s configuration `c`, read
relative to the heads. -/
private def tt_rep {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) (D : ZoneData k) :
    Prop :=
  ∀ t p, zoneTrackTape (D.2 t) p = c.workTapes t (c.workTapePos t + p)

/-- Under the represented-tape invariant, the homes are the symbols under `M`'s heads. -/
private theorem tt_rep_home {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x)
    (D : ZoneData k) (h : tt_rep c D) : (fun t => (D.2 t).home) = c.workTapeSymbols := by
  funext t
  rw [Cfg.workTapeSymbols_eq, ← zoneTrackTape_zero, h t 0, add_zero]

/-- **One round preserves the invariant** [HS66; AB09, §1.7]: if `D` is full and represents
the work tapes of `M`'s live configuration `c` at `q`, then the round's data represent the work
tapes of `M`'s next configuration and are full. The action the round computes from the homes is
`M`'s own.

**Proof sketch.** The homes are the symbols under the heads (`tt_rep_home`), so the round's
action is `M`'s (`Turing.MultiTapeTM.step_of_some`). The home write puts the written symbol at
position `0` (`tt_homeData_inv`) and the tracks shift each represented tape by its head's
move (`tt_Dtr_inv`); `M`'s step writes at its head and then moves it
(`Turing.Action.apply_workTapes`, `Turing.Action.apply_workTapePos`), which is the same tape read
from the moved head. -/
private theorem tt_round_inv (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x)
    (q : M.State) (hq : c.state = some q) (D : ZoneData M.k) (hD : tt_fullD D)
    (hrep : tt_rep c D) :
    tt_act M q c.inputSymbol D = M.tm.tr q c.inputSymbol c.workTapeSymbols ∧
      tt_fullD (tt_roundData (tt_act M q c.inputSymbol D) D) ∧
      tt_rep (M.tm.step c) (tt_roundData (tt_act M q c.inputSymbol D) D) := by
  have hact : tt_act M q c.inputSymbol D = M.tm.tr q c.inputSymbol c.workTapeSymbols := by
    show M.tm.tr q c.inputSymbol (fun t => (D.2 t).home) = _
    rw [tt_rep_home c D hrep]
  set a := tt_act M q c.inputSymbol D with ha
  obtain ⟨hf₁, htape₁⟩ := tt_homeData_inv a D hD
  obtain ⟨hf₂, htape₂⟩ := tt_Dtr_inv (tt_moves a) (tt_homeData a D) hf₁ M.k
  refine ⟨hact, hf₂, fun t p => ?_⟩
  show zoneTrackTape ((tt_Dtr (tt_moves a) (tt_homeData a D) M.k).2 t) p = _
  rw [htape₂, if_pos t.isLt, htape₁, MultiTapeTM.step_of_some hq, Action.apply_workTapes,
    Action.apply_workTapePos, ← hact, ← tt_rep_home c D hrep]
  rw [show (a.workTapes t).1.getD ((fun t => (D.2 t).home) t) =
      tt_homeNew a (fun t => (D.2 t).home) t from rfl,
    show (a.workTapes t).2 = tt_moves a t from rfl]
  by_cases hp : p + (tt_moves a t : ℤ) = 0
  · rw [if_pos hp, show c.workTapePos t + (tt_moves a t : ℤ) + p = c.workTapePos t by omega,
      Function.update_self]
  · rw [if_neg hp, Function.update_of_ne (by omega), hrep t]
    congr 1
    ring

/-! ### The data orbit -/

/-- `M`'s run on `x`: its configuration after `r` steps. -/
private def tt_c (M : FinTM Bool) (x : List Bool) (r : ℕ) : Cfg M.k Bool M.State x :=
  M.tm.runFrom (M.tm.initCfg x) r

/-- **The data orbit** of the simulation of `M` on `x` [HS66; AB09, §1.7]: no level and empty
tracks at first; after each live step of `M`, the data after the round that simulates it. -/
private def tt_D (M : FinTM Bool) (x : List Bool) : ℕ → ZoneData M.k
  | 0 => ⟨0, fun _ => ZoneContents.empty 0⟩
  | r + 1 =>
    match (tt_c M x r).state with
    | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
    | none => tt_D M x r

/-- The orbit's step at a live configuration. -/
private theorem tt_D_succ (M : FinTM Bool) (x : List Bool) (r : ℕ) (q : M.State)
    (hq : (tt_c M x r).state = some q) :
    tt_D M x (r + 1) = tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r))
      (tt_D M x r) := by
  show (match (tt_c M x r).state with
    | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
    | none => tt_D M x r) = _
  rw [hq]

/-- **The invariant along the orbit** [HS66; AB09, §1.7]: at every time `r` the data are full
and represent the work tapes of `M`'s configuration after `r` steps.

**Proof sketch.** Induction on `r`. At `0` the tracks are empty and represent blank tapes
(`Turing.zoneTrackTape_empty`), as `M`'s initial work tapes are (`Turing.Cfg.init_workTapes`).
A live step is `tt_round_inv`, `M`'s next configuration being its step
(`Turing.MultiTapeTM.runFrom_succ_eq_step'`); a halted one changes neither side
(`Turing.MultiTapeTM.step_of_halt`). -/
private theorem tt_D_inv (M : FinTM Bool) (x : List Bool) (r : ℕ) :
    tt_fullD (tt_D M x r) ∧ tt_rep (tt_c M x r) (tt_D M x r) := by
  induction r with
  | zero =>
    refine ⟨fun _ => tt_full_empty, fun t p => ?_⟩
    show zoneTrackTape (ZoneContents.empty 0) p =
      (M.tm.runFrom (M.tm.initCfg x) 0).workTapes t _
    rw [zoneTrackTape_empty, MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq,
      Cfg.init_workTapes]
  | succ r ih =>
    have hc : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
    cases hq : (tt_c M x r).state with
    | none =>
      rw [hc, MultiTapeTM.step_of_halt hq]
      show tt_fullD (match (tt_c M x r).state with
        | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
        | none => tt_D M x r) ∧ tt_rep (tt_c M x r) (match (tt_c M x r).state with
        | some q => tt_roundData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r)
        | none => tt_D M x r)
      rw [hq]
      exact ih
    | some q =>
      rw [tt_D_succ M x r q hq, hc]
      exact (tt_round_inv M (tt_c M x r) q hq _ ih.1 ih.2).2

/-! ### The run: the configurations at the round boundaries and the iteration -/

/-- Moving input heads at equal positions over inputs of equal length gives equal positions. -/
private theorem tt_moveInputPos_val {n n' : ℕ} (hn : n = n') (p : Fin (n + 2)) (p' : Fin (n' + 2))
    (h : p.val = p'.val) (s : SignType) : (moveInputPos p s).val = (moveInputPos p' s).val := by
  subst hn
  rw [Fin.ext h]

/-- **The decoded input symbol** of a configuration on the encoded input `x.map Sum.inl` is the
input symbol of a configuration on `x` with the input head at the same position.

**Proof sketch.** Lift `c` along `Sum.inl` (`Turing.Cfg.liftSymbols`): the lift is on the
encoded input with `c`'s input head, so `d` reads what it reads (`Turing.Cfg.inputSymbol_congr`),
namely `c`'s input symbol mapped by `Sum.inl` (`Turing.Cfg.liftSymbols_inputSymbol`), which
`tt_decodeIn` decodes back. -/
private theorem tt_inputSymbol {k k' : ℕ} {S S' : Type} {x : List Bool}
    (d : Cfg k (ZoneSym k') S (x.map Sum.inl)) (c : Cfg k' Bool S' x)
    (h : d.inputPos.val = c.inputPos.val) : tt_decodeIn d.inputSymbol = c.inputSymbol := by
  rw [Cfg.inputSymbol_congr d (c.liftSymbols Function.Embedding.inl)
    (by rw [Cfg.liftSymbols_inputPos, Fin.coe_cast]; exact h), Cfg.liftSymbols_inputSymbol]
  cases c.inputSymbol <;> rfl

/-- The input position of `M`'s configuration on `x`, as a position on the encoded input. -/
private def tt_ipOf (M : FinTM Bool) {x : List Bool} (c : Cfg M.k Bool M.State x) :
    Fin ((x.map (Sum.inl : Bool → ZoneSym M.k)).length + 2) :=
  ⟨c.inputPos.val, by rw [List.length_map]; exact c.inputPos.isLt⟩

/-- **The zone machine's configurations at the round boundaries** [HS66; AB09, §1.7]: its
initial configuration, and after `r + 1` rounds the transition step at `M`'s state after
`r + 1` steps, with the orbit's data, `M`'s input position and `M`'s output encoded. -/
private def tt_cs (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool) :
    ℕ → Cfg 2 (ZoneSym M.k) (Σ i, tt_Ph M F i) (x.map Sum.inl)
  | 0 => Cfg.init ⟨none, .inl M.tm.q₀⟩ (x.map Sum.inl)
  | r + 1 => tt_cfg ((tt_c M x (r + 1)).state.map fun q => ⟨none, .inl q⟩) (tt_D M x (r + 1))
      (tt_ipOf M (tt_c M x (r + 1))) ((tt_c M x (r + 1)).output.map Sum.inl)

/-- **The length of round `r`**: two steps for the transition step and its dispatch, and each
track's phase with its dispatch step; `0` once `M` has halted. -/
private def tt_T (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool) (r : ℕ) : ℕ :=
  match (tt_c M x r).state with
  | some q =>
    2 + ∑ j ∈ Finset.range M.k, tt_τ M F (x.map Sum.inl)
      (tt_moves (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)))
      (tt_homeData (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r))
      (moveInputPos (tt_ipOf M (tt_c M x r))
        (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)).inputTape)
      ((tt_c M x r).output.map Sum.inl ++
        ((tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)).output.map Sum.inl).toList) j
  | none => 0

/-- **A round's start is a transition-step configuration** of `tt_round`: at a live time `r`,
the boundary configuration is the transition step at `M`'s state, renamed into the host, with a
home cell that reads the orbit's homes (blank in the first round, the zoned tape's later).

**Proof sketch.** At `r = 0` the host's initial configuration (`Turing.Cfg.init`'s fields) has
blank tapes, which is the zoned tape of the empty contents off the home cell
(`Turing.zonedTape_blank_outside`, `Turing.zoneStart_eq`) with a blank home; a blank home reads
blank (`Turing.zoneCellOfCell_none`), as the empty contents' homes are. Later a boundary
configuration's home cell is the zoned tape's own (`Function.update_eq_self`), which reads the
homes (`Turing.zonedTape_zero`, `Turing.zoneCellOfCell_inr`). Field by field through
`Turing.Cfg.mapState_eq_of_fields`. -/
private theorem tt_cs_start (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool)
    (r : ℕ) (q : M.State) (hq : (tt_c M x r).state = some q) :
    ∃ h0 : Option (ZoneSym M.k), (∀ t, tt_homeRead h0 t = ((tt_D M x r).2 t).home) ∧
      tt_cs M F x r = (tt_cfg0 (some (.inl q)) (tt_D M x r) h0 (tt_ipOf M (tt_c M x r))
        ((tt_c M x r).output.map Sum.inl) :
          Cfg 2 (ZoneSym M.k) (tt_LeafSt M) (x.map Sum.inl)).mapState (Sigma.mk none) := by
  cases r with
  | zero =>
    have hc : tt_c M x 0 = Cfg.init M.tm.q₀ x := by
      show M.tm.runFrom (M.tm.initCfg x) 0 = _
      rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq]
    rw [hc, Cfg.init_state] at hq
    obtain rfl := Option.some.inj hq
    refine ⟨none, fun t => ?_, ?_⟩
    · show (zoneCellOfCell none t).join = (ZoneContents.empty 0).home
      rw [zoneCellOfCell_none, ZoneContents.empty_home]
      rfl
    · show Cfg.init (⟨none, .inl M.tm.q₀⟩ : Σ i, tt_Ph M F i) (x.map Sum.inl) = _
      refine (Cfg.mapState_eq_of_fields _ _ _ ?_ ?_ ?_ ?_ ?_).symm
      · rw [Cfg.init_state]
        rfl
      · rw [Cfg.init_inputPos]
        refine Fin.ext ?_
        show (tt_c M x 0).inputPos.val = _
        rw [hc, Cfg.init_inputPos]
        rfl
      · funext j p
        rw [Cfg.init_workTapes]
        by_cases hj : j = 0
        · subst hj
          show Function.update (zonedTape (fun _ => ZoneContents.empty 0)) 0 none p = none
          by_cases hp : p = 0
          · subst hp
            exact Function.update_self _ _ _
          · rw [Function.update_of_ne hp]
            refine zonedTape_blank_outside _ p ?_
            rw [zoneStart_eq]
            have : (1 : ℤ) ≤ |p| := Int.one_le_abs hp
            norm_num
            omega
        · show (if j = 0 then _ else fun _ => none) p = none
          rw [if_neg hj]
      · funext j
        rw [Cfg.init_workTapePos]
        rfl
      · rw [Cfg.init_output]
        show (tt_c M x 0).output.map Sum.inl = []
        rw [hc, Cfg.init_output, List.map_nil]
  | succ r =>
    refine ⟨zonedTape (tt_D M x (r + 1)).2 0, fun t => ?_, ?_⟩
    · rw [tt_homeRead, zonedTape_zero, zoneCellOfCell_inr]
      rfl
    · show tt_cfg _ _ _ _ = _
      rw [hq]
      apply Eq.symm
      refine Cfg.mapState_eq_of_fields _ _ _ rfl rfl ?_ rfl rfl
      funext j p
      by_cases hj : j = 0
      · subst hj
        show Function.update (zonedTape (tt_D M x (r + 1)).2) 0
          (zonedTape (tt_D M x (r + 1)).2 0) p = zonedTape (tt_D M x (r + 1)).2 p
        rw [Function.update_eq_self]
      · show (if j = 0 then _ else fun _ => none) p = (if j = 0 then _ else fun _ => none) p
        rw [if_neg hj, if_neg hj]

/-- **One round of the run** [HS66; AB09, §1.7]: while `M` is live after `r + 1` steps, the
zone machine runs live from the boundary configuration after `r` rounds to the one after
`r + 1`, in `tt_T` steps.

**Proof sketch.** `M` is live at `r` too (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`).
The start is a transition-step configuration (`tt_cs_start`), and the round's action is `M`'s
(`tt_round_inv`), whose successor state is `M`'s next state (`Turing.Action.apply_state`).
`tt_round` gives the segment; its endpoint is the next boundary configuration: the data are the
orbit's next (`tt_D_succ`), the input head moves as `M`'s (`tt_moveInputPos_val`,
`Turing.Action.apply_inputPos`) and the output gains the encoded emission
(`Turing.Action.apply_output`, `Option.toList_map`). -/
private theorem tt_cs_round (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (r : ℕ) (hr : (tt_c M x (r + 1)).state ≠ none) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cs M F x r) (tt_cs M F x (r + 1)) (tt_T M F x r) := by
  have hlive : (tt_c M x r).state ≠ none :=
    MultiTapeTM.runFrom_state_ne_none_of_le _ _ (r + 1) hr r (Nat.le_succ r)
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
  obtain ⟨q', hq'⟩ := Option.ne_none_iff_exists'.mp hr
  have hstep : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
  obtain ⟨hact, -, -⟩ := tt_round_inv M (tt_c M x r) q hq _ (tt_D_inv M x r).1 (tt_D_inv M x r).2
  set a := tt_act M q (tt_c M x r).inputSymbol (tt_D M x r) with ha
  have happly : tt_c M x (r + 1) = a.apply (tt_c M x r) := by
    rw [hstep, MultiTapeTM.step_of_some hq, ← hact]
  have hsa : a.state = some q' := by
    rw [← hq', happly, Action.apply_state]
  obtain ⟨h0, hread, hstart⟩ := tt_cs_start M F x r q hq
  have hinp : tt_decodeIn (tt_cfg0 (some (.inl q)) (tt_D M x r) h0 (tt_ipOf M (tt_c M x r))
      ((tt_c M x r).output.map Sum.inl) :
        Cfg 2 (ZoneSym M.k) (tt_LeafSt M) (x.map Sum.inl)).inputSymbol =
      (tt_c M x r).inputSymbol :=
    tt_inputSymbol _ _ rfl
  have H := (tt_round M F hk q (tt_D M x r) h0 hread (tt_ipOf M (tt_c M x r))
    ((tt_c M x r).output.map Sum.inl) _ hinp).2 q' hsa
  have hT : tt_T M F x r = 2 + ∑ j ∈ Finset.range M.k, tt_τ M F (x.map Sum.inl) (tt_moves a)
      (tt_homeData a (tt_D M x r)) (moveInputPos (tt_ipOf M (tt_c M x r)) a.inputTape)
      ((tt_c M x r).output.map Sum.inl ++ (a.output.map Sum.inl).toList) j := by
    show (match (tt_c M x r).state with
      | some q => _
      | none => 0) = _
    rw [hq]
  have hend : tt_cs M F x (r + 1) = tt_cfg (some ⟨none, .inl q'⟩)
      (tt_Dtr (tt_moves a) (tt_homeData a (tt_D M x r)) M.k)
      (moveInputPos (tt_ipOf M (tt_c M x r)) a.inputTape)
      ((tt_c M x r).output.map Sum.inl ++ (a.output.map Sum.inl).toList) := by
    show tt_cfg _ _ _ _ = _
    rw [hq', tt_D_succ M x r q hq]
    congr 1
    · refine Fin.ext ?_
      show (tt_c M x (r + 1)).inputPos.val = _
      rw [happly, Action.apply_inputPos]
      exact tt_moveInputPos_val (List.length_map _).symm _ _ rfl _
    · rw [happly, Action.apply_output, List.map_append, Option.toList_map]
  rw [hstart, hT, hend]
  exact H

/-- **The run through the first `s` rounds** [HS66; AB09, §1.7]: while `M` is live after `s`
steps, the zone machine runs live from its initial configuration to the boundary configuration
after `s` rounds, in the rounds' summed time.

**Proof sketch.** `Turing.Segment.iterate_seq` over the rounds (`tt_cs_round`), each round's
liveness from `M`'s at `s` (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`). -/
private theorem tt_cs_run (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (s : ℕ) (hs : (tt_c M x s).state ≠ none) :
    Segment (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)) {none}
      (fun _ => True) (tt_cs M F x 0) (tt_cs M F x s)
      (∑ r ∈ Finset.range s, tt_T M F x r) :=
  Segment.iterate_seq (tt_cs M F x) (tt_T M F x) trivial s fun r hr =>
    tt_cs_round M F hk x r (MultiTapeTM.runFrom_state_ne_none_of_le _ _ s hs (r + 1) hr)

/-- **The halting round** [HS66; AB09, §1.7]: if `M` is live after `r` steps and halted after
`r + 1`, the zone machine halts one step after the boundary configuration of round `r`, with
`M`'s output encoded.

**Proof sketch.** The start is a transition-step configuration (`tt_cs_start`); the round's
action is `M`'s (`tt_round_inv`) and halts with it; `tt_round`'s halting clause gives the halt
and the output, which is `M`'s after its last step (`Turing.Action.apply_output`). -/
private theorem tt_cs_halt (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (r : ℕ) (hr : (tt_c M x r).state ≠ none)
    (hh : (tt_c M x (r + 1)).state = none) :
    ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x r) 1).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x r) 1).output = (tt_c M x (r + 1)).output.map Sum.inl := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hr
  have hstep : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
  obtain ⟨hact, -, -⟩ := tt_round_inv M (tt_c M x r) q hq _ (tt_D_inv M x r).1 (tt_D_inv M x r).2
  set a := tt_act M q (tt_c M x r).inputSymbol (tt_D M x r) with ha
  have happly : tt_c M x (r + 1) = a.apply (tt_c M x r) := by
    rw [hstep, MultiTapeTM.step_of_some hq, ← hact]
  have hsa : a.state = none := by
    rw [← hh, happly, Action.apply_state]
  obtain ⟨h0, hread, hstart⟩ := tt_cs_start M F x r q hq
  have H := (tt_round M F hk q (tt_D M x r) h0 hread (tt_ipOf M (tt_c M x r))
    ((tt_c M x r).output.map Sum.inl) _ (tt_inputSymbol _ _ rfl)).1 hsa
  rw [hstart]
  refine ⟨H.1, ?_⟩
  rw [H.2, happly, Action.apply_output, List.map_append, Option.toList_map]

/-- **Every round takes at least two steps** while `M` is live: the transition step and its
dispatch. -/
private theorem tt_T_ge (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (x : List Bool) (r : ℕ)
    (hr : (tt_c M x r).state ≠ none) : 2 ≤ tt_T M F x r := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hr
  show 2 ≤ (match (tt_c M x r).state with
    | some q => _
    | none => 0)
  rw [hq]
  exact Nat.le_add_right _ _

/-- The zone machine's initial configuration is the boundary configuration before any round. -/
private theorem tt_HS_init (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) : (tt_HS M F hk).tm.initCfg (x.map Sum.inl) = tt_cs M F x 0 := by
  show (phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).initCfg (x.map Sum.inl) =
    Cfg.init ⟨none, .inl M.tm.q₀⟩ (x.map Sum.inl)
  rw [MultiTapeTM.initCfg_eq, phaseHostTM_q₀]

/-- **The zone machine reproduces a halting run** [HS66; AB09, §1.7]: if `M` halts on `x`
within `t` steps with output `o`, it first halts at some `t₀ ≤ t`, live before, and the zone
machine halts on `x.map Sum.inl` with `o.map Sum.inl` after the first `t₀ - 1` rounds and one
more step.

**Proof sketch.** The first halt (`Turing.MultiTapeTM.exists_first_halt`) is positive, as the
initial configuration is live. The rounds before it run as one segment (`tt_cs_run`), and the
last transition halts (`tt_cs_halt`) with `M`'s output, which is `o`; the two concatenate by
`Turing.MultiTapeTM.runFrom_add`. -/
private theorem tt_forward_run (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x o : List Bool) (t : ℕ) (h : M.ComputesInTime x o t) :
    ∃ t₀, t₀ ≤ t ∧ 1 ≤ t₀ ∧ (∀ r < t₀, (tt_c M x r).state ≠ none) ∧
      (tt_HS M F hk).ComputesInTime (x.map Sum.inl) (o.map Sum.inl)
        (∑ r ∈ Finset.range (t₀ - 1), tt_T M F x r + 1) := by
  obtain ⟨hs, ho⟩ := (computesInTime_iff M x o t).1 h
  obtain ⟨u, hu, hlive, heq⟩ := MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg x) hs
  have hc : ∀ r, tt_c M x r = M.tm.runFrom (M.tm.initCfg x) r := fun _ => rfl
  cases u with
  | zero =>
    exfalso
    have h0 : (M.tm.runFrom (M.tm.initCfg x) 0).state = none := heq ▸ hs
    exact not_computesInTime_zero M x _ ((computesInTime_iff M x _ 0).2 ⟨h0, rfl⟩)
  | succ s =>
    have hl : ∀ r < s + 1, (tt_c M x r).state ≠ none := fun r hr => hlive r hr
    refine ⟨s + 1, hu, Nat.le_add_left 1 s, hl, ?_⟩
    rw [Nat.add_sub_cancel]
    have hseg := tt_cs_run M F hk x s (hl s (Nat.lt_succ_self s))
    have hhalt : (tt_c M x (s + 1)).state = none := by rw [hc, heq]; exact hs
    obtain ⟨h1, h2⟩ := tt_cs_halt M F hk x s (hl s (Nat.lt_succ_self s)) hhalt
    rw [segment_iff] at hseg
    rw [computesInTime_iff, tt_HS_init]
    show ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x 0) _).state = none ∧
      ((phaseHostTM (tt_Mf M F) ⟨none, .inl M.tm.q₀⟩ (tt_red M F hk)).runFrom
        (tt_cs M F x 0) _).output = _
    rw [MultiTapeTM.runFrom_add, hseg.1]
    refine ⟨h1, ?_⟩
    rw [h2, hc, heq, ho]

/-- **Every completed output of the zone machine is an encoded output of `M`** [HS66; AB09,
§1.7].

**Proof sketch.** If `M` never halted on `x`, the first `t' + 1` rounds would run live for at
least `2 (t' + 1)` steps (`tt_cs_run`, `tt_T_ge`), so the zone machine would be live at `t'`.
Hence `M` halts at some time with some output `v`; then the zone machine halts with
`v.map Sum.inl` (`tt_forward_run`), and a completed output is unique
(`Turing.FinTM.ComputesInTime.output_unique`). -/
private theorem tt_converse (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (o' : List (ZoneSym M.k)) (t' : ℕ)
    (h : (tt_HS M F hk).ComputesInTime (x.map Sum.inl) o' t') :
    ∃ (t : ℕ) (v : List Bool), M.ComputesInTime x v t ∧ o' = v.map Sum.inl := by
  by_cases hhalt : ∃ s, (tt_c M x s).state = none
  · obtain ⟨s, hs⟩ := hhalt
    have hM : M.ComputesInTime x (tt_c M x s).output s :=
      (computesInTime_iff M x _ s).2 ⟨hs, rfl⟩
    obtain ⟨_, -, -, -, hHS⟩ := tt_forward_run M F hk x _ s hM
    exact ⟨s, _, hM, h.output_unique hHS⟩
  · exfalso
    push_neg at hhalt
    have hseg := tt_cs_run M F hk x (t' + 1) (hhalt _)
    have hsum : 2 * (t' + 1) ≤ ∑ r ∈ Finset.range (t' + 1), tt_T M F x r := by
      have h := Finset.card_nsmul_le_sum (Finset.range (t' + 1)) (tt_T M F x) 2
        fun r _ => tt_T_ge M F x r (hhalt r)
      rwa [Finset.card_range, Nat.nsmul_eq_mul, Nat.mul_comm (t' + 1) 2] at h
    obtain ⟨hs, -⟩ := (computesInTime_iff _ _ _ _).1 h
    rw [tt_HS_init] at hs
    exact (segment_iff _ _ _ _ _ _).1 hseg |>.2.1 t' (by omega) (Set.mem_singleton_iff.mpr hs)

/-! ### Side totals -/

/-- **The side total** of one track below level `n`: the number of cells stored in its right
zones of levels `< n` (levels not laid out count `0`). -/
private def tt_rsum {ℓ : ℕ} (z : ZoneContents ℓ) (n : ℕ) : ℕ :=
  ∑ l ∈ Finset.range n, if h : l < ℓ then (z.right ⟨l, h⟩).length else 0

/-- One more level of the side total. -/
private theorem tt_rsum_succ {ℓ : ℕ} (z : ZoneContents ℓ) (n : ℕ) (hn : n < ℓ) :
    tt_rsum z (n + 1) = tt_rsum z n + (z.right ⟨n, hn⟩).length := by
  rw [tt_rsum, Finset.sum_range_succ, dif_pos hn]
  rfl

/-- **Below the scanned index, the side total is extreme** [AB09, §1.7]: under fullness, below
the scanned index `j` of a move in direction `dir` the feeding zones are empty, so the right
zones of levels `< n ≤ j` hold nothing (a right move) or everything (a left move:
`2^{n+1} − 2` cells).

**Proof sketch.** Induction on `n`: the level `n < j` is empty on the feeding side
(`Turing.zoneShiftIndex_empty`), so by fullness its right zone holds `0` cells (a right move) or
the whole capacity `2 · 2^n` (a left move), and `2^{n+1} − 2 + 2^{n+1} = 2^{n+2} − 2`. -/
private theorem tt_rsum_low {ℓ : ℕ} (dir : Bool) (z : ZoneContents ℓ) (hz : tt_full z) (n : ℕ)
    (hn : n ≤ zoneShiftIndex dir z) (hnℓ : n ≤ ℓ) :
    tt_rsum z n = if dir then 0 else 2 ^ (n + 1) - 2 := by
  induction n with
  | zero => cases dir <;> rfl
  | succ n ih =>
    rw [tt_rsum_succ z n (by omega), ih (by omega) (by omega)]
    have he := zoneShiftIndex_empty dir z ⟨n, by omega⟩ (by show n < _; omega)
    cases dir
    · rw [ZoneContents.words_false] at he
      have hs := (hz ⟨n, by omega⟩).1
      rw [he, List.length_nil, zero_add, zoneCapacity_eq] at hs
      show 2 ^ (n + 1) - 2 + (z.right ⟨n, _⟩).length = 2 ^ (n + 1 + 1) - 2
      have h1 : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
      rw [show (z.right ⟨n, _⟩).length = 2 * 2 ^ n from hs, pow_succ, pow_succ]
      rw [pow_succ] at h1
      omega
    · rw [ZoneContents.words_true] at he
      show 0 + (z.right ⟨n, _⟩).length = 0
      rw [he]
      rfl

/-- **A right rebalance moves one cell off the right side** [AB09, §1.7]: under fullness, with
scanned index `j < ℓ`, the rebalanced side total below `n` is `2^n − 1` for `n ≤ j` (the levels
below `j` half full), and one less than before for `j < n ≤ ℓ`.

**Proof sketch.** Induction on `n`, reading the levels through `tt_full_rebalance_true` below
`j`, `Turing.zoneCascadeRight_lengths` at `j` under the pre-state `tt_full_pre_true` (the donor
loses `2^j` cells, which fill the `2^j − 1` cells below and the home), and
`Turing.zoneRebalance_frame` above `j`. -/
private theorem tt_rsum_rebalance_true {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex true z < ℓ) (n : ℕ) (hnℓ : n ≤ ℓ) :
    (n ≤ zoneShiftIndex true z → tt_rsum (zoneRebalance true z) n = 2 ^ n - 1) ∧
      (zoneShiftIndex true z < n → tt_rsum (zoneRebalance true z) n + 1 = tt_rsum z n) := by
  set j := zoneShiftIndex true z with hj
  obtain ⟨hr, hl, hdonor, hroom⟩ := tt_full_pre_true z hz hj.symm h
  have hlow := (tt_full_rebalance_true z hz h).2
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame true z k hk
  have hz0 := tt_rsum_low true z hz j le_rfl h.le
  have hcas := zoneCascadeRight_lengths j h z hr hl hdonor hroom
  clear hr
  induction n with
  | zero => exact ⟨fun _ => rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    rw [tt_rsum_succ _ n (by omega), tt_rsum_succ z n (by omega)]
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [ih₁ (by omega), (hlow ⟨n, by omega⟩ (by show n < j; omega)).2]
      show 2 ^ n - 1 + 2 ^ n = 2 ^ (n + 1) - 1
      have := Nat.one_le_two_pow (n := n)
      rw [pow_succ]
      omega
    · rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [(hframe ⟨n, by omega⟩ hjn).2, ← ih₂ hjn]
        omega
      · have hnj : n = j := by omega
        have hfin : (⟨n, (by omega : n < ℓ)⟩ : Fin ℓ) = ⟨j, h⟩ := Fin.ext hnj
        obtain ⟨-, hjr, -⟩ := hcas
        have hj' : ((zoneRebalance true z).right ⟨j, h⟩).length =
            (z.right ⟨j, h⟩).length - 2 ^ j := by
          rw [zoneRebalance_of_lt true z h, zoneCascade_true]
          exact hjr
        have hz0' : tt_rsum z j = 0 := by rw [hz0]; rfl
        rw [hfin, ih₁ hnj.le, hnj, hz0', hj']
        have := Nat.one_le_two_pow (n := j)
        omega

/-- **A left rebalance moves one cell onto the right side**: the mirror of
`tt_rsum_rebalance_true`; the side total below `n ≤ j` is `2^n − 1`, and for `j < n ≤ ℓ` it is
one more than before.

**Proof sketch.** As for `tt_rsum_rebalance_true`, with `tt_full_rebalance_false` below the
index, `Turing.zoneCascadeLeft_lengths` at it under the pre-state `tt_full_pre_false` (the right
zone gains `2^j` cells, while the right zones below drop from full to half: `2^{j+1} − 2` cells
become `2^j − 1`), and `Turing.zoneRebalance_frame` above. -/
private theorem tt_rsum_rebalance_false {ℓ : ℕ} (z : ZoneContents ℓ) (hz : tt_full z)
    (h : zoneShiftIndex false z < ℓ) (n : ℕ) (hnℓ : n ≤ ℓ) :
    (n ≤ zoneShiftIndex false z → tt_rsum (zoneRebalance false z) n = 2 ^ n - 1) ∧
      (zoneShiftIndex false z < n → tt_rsum (zoneRebalance false z) n = tt_rsum z n + 1) := by
  set j := zoneShiftIndex false z with hj
  obtain ⟨hl, hr, hdonor, hroom⟩ := tt_full_pre_false z hz hj.symm h
  have hlow := (tt_full_rebalance_false z hz h).2
  have hframe := fun (k : Fin ℓ) (hk : j < k.val) => zoneRebalance_frame false z k hk
  have hz0 := tt_rsum_low false z hz j le_rfl h.le
  have hcas := zoneCascadeLeft_lengths j h z hl hr hdonor hroom
  clear hl
  induction n with
  | zero => exact ⟨fun _ => rfl, fun h' => absurd h' (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨ih₁, ih₂⟩ := ih (by omega)
    rw [tt_rsum_succ _ n (by omega), tt_rsum_succ z n (by omega)]
    refine ⟨fun hn => ?_, fun hn => ?_⟩
    · rw [ih₁ (by omega), (hlow ⟨n, by omega⟩ (by show n < j; omega)).2]
      show 2 ^ n - 1 + 2 ^ n = 2 ^ (n + 1) - 1
      have := Nat.one_le_two_pow (n := n)
      rw [pow_succ]
      omega
    · rcases Nat.lt_or_ge j n with hjn | hjn
      · rw [(hframe ⟨n, by omega⟩ hjn).2, ih₂ hjn]
        omega
      · have hnj : n = j := by omega
        have hfin : (⟨n, (by omega : n < ℓ)⟩ : Fin ℓ) = ⟨j, h⟩ := Fin.ext hnj
        obtain ⟨-, -, hjr⟩ := hcas
        have hj' : ((zoneRebalance false z).right ⟨j, h⟩).length =
            (z.right ⟨j, h⟩).length + 2 ^ j := by
          rw [zoneRebalance_of_lt false z h, zoneCascade_false]
          exact hjr
        have hz0' : tt_rsum z j = 2 ^ (j + 1) - 2 := by rw [hz0]; rfl
        rw [hfin, ih₁ hnj.le, hnj, hz0', hj']
        have := Nat.one_le_two_pow (n := j)
        rw [pow_succ]
        omega

/-- The home write keeps every side total. -/
private theorem tt_rsum_homeWrite {ℓ : ℕ} (z : ZoneContents ℓ) (v : Option Bool) (n : ℕ) :
    tt_rsum (zoneHomeWrite z v) n = tt_rsum z n := by
  unfold tt_rsum
  simp only [zoneHomeWrite_right]

/-- **The extension keeps the side totals of the old levels and adds `2^ℓ` at the new one**
(`Turing.ZoneContents.extend_words_castSucc`, `_last`). -/
private theorem tt_rsum_extend {ℓ : ℕ} (z : ZoneContents ℓ) :
    (∀ n ≤ ℓ, tt_rsum z.extend n = tt_rsum z n) ∧
      tt_rsum z.extend (ℓ + 1) = tt_rsum z ℓ + 2 ^ ℓ := by
  have hold : ∀ n ≤ ℓ, tt_rsum z.extend n = tt_rsum z n := by
    intro n hn
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl' : l < ℓ := by have := Finset.mem_range.mp hl; omega
    rw [dif_pos hl', dif_pos (by omega)]
    have := ZoneContents.extend_words_castSucc true z ⟨l, hl'⟩
    rw [ZoneContents.words_true, ZoneContents.words_true] at this
    exact congrArg List.length this
  refine ⟨hold, ?_⟩
  rw [tt_rsum_succ _ ℓ (Nat.lt_succ_self ℓ), hold ℓ le_rfl]
  have := ZoneContents.extend_words_last true z
  rw [ZoneContents.words_true] at this
  rw [show (⟨ℓ, Nat.lt_succ_self ℓ⟩ : Fin (ℓ + 1)) = Fin.last ℓ from rfl, this,
    List.length_replicate]

/-- **One track's step on the side totals** [AB09, §1.7]. Under fullness, with `j` the scanned
index of track `t`'s step in direction `dir` and `ℓ = D.1`:
* track `t`'s side totals below `n ≤ min ℓ j` become `2^n − 1`;
* for `j < n ≤ ℓ` they move by the head's displacement (`tt_shift dir` cells leave the right
  side);
* its whole side total moves by the displacement, plus `2^ℓ` after an extension;
* every other track keeps its side totals below `ℓ`, and its whole side total gains `2^ℓ` after
  an extension;
* the level count is `ℓ`, or `ℓ + 1` after an extension.

**Proof sketch.** With a nonempty feeding zone (`Turing.zoneTrackStepData_of_lt`,
`Turing.zoneRebalanceData_eq`) this is `tt_rsum_rebalance_true`/`_false` on track `t` and
`Function.update_of_ne` elsewhere. Otherwise (`Turing.zoneTrackStepData_of_not_lt`,
`Turing.zoneExtendData_eq`) the scanned index is `ℓ`, every track is extended
(`tt_rsum_extend`), and track `t` is rebalanced at the new level `ℓ`
(`Turing.zoneShiftIndex_extend`, `tt_full_extend`). -/
private theorem tt_trackStep_rsum {k : ℕ} (dir : Bool) (t : Fin k) (D : ZoneData k)
    (hD : tt_fullD D) :
    (∀ n, n ≤ D.1 → n ≤ zoneRebalanceIndex dir t D →
      tt_rsum ((zoneTrackStepData dir t D).2 t) n = 2 ^ n - 1) ∧
    (∀ n, n ≤ D.1 → zoneRebalanceIndex dir t D < n →
      (tt_rsum ((zoneTrackStepData dir t D).2 t) n : ℤ) = tt_rsum (D.2 t) n - tt_shift dir) ∧
    ((tt_rsum ((zoneTrackStepData dir t D).2 t) (zoneTrackStepData dir t D).1 : ℤ) =
      tt_rsum (D.2 t) D.1 - tt_shift dir +
        (if zoneRebalanceIndex dir t D < D.1 then 0 else 2 ^ D.1)) ∧
    (∀ t', t' ≠ t →
      (∀ n, n ≤ D.1 → tt_rsum ((zoneTrackStepData dir t D).2 t') n = tt_rsum (D.2 t') n) ∧
      tt_rsum ((zoneTrackStepData dir t D).2 t') (zoneTrackStepData dir t D).1 =
        tt_rsum (D.2 t') D.1 + (if zoneRebalanceIndex dir t D < D.1 then 0 else 2 ^ D.1)) ∧
    (zoneTrackStepData dir t D).1 =
      (if zoneRebalanceIndex dir t D < D.1 then D.1 else D.1 + 1) := by
  have hreb : ∀ {ℓ : ℕ} (z : ZoneContents ℓ), tt_full z → zoneShiftIndex dir z < ℓ →
      ∀ n, n ≤ ℓ → (n ≤ zoneShiftIndex dir z → tt_rsum (zoneRebalance dir z) n = 2 ^ n - 1) ∧
        (zoneShiftIndex dir z < n →
          (tt_rsum (zoneRebalance dir z) n : ℤ) = tt_rsum z n - tt_shift dir) := by
    intro ℓ z hz h n hn
    cases dir
    · obtain ⟨h1, h2⟩ := tt_rsum_rebalance_false z hz h n hn
      refine ⟨h1, fun h' => ?_⟩
      rw [h2 h']
      push_cast
      show _ = _ - (-1 : ℤ)
      ring
    · obtain ⟨h1, h2⟩ := tt_rsum_rebalance_true z hz h n hn
      refine ⟨h1, fun h' => ?_⟩
      rw [← h2 h']
      push_cast
      show _ = _ - (1 : ℤ)
      ring
  rw [zoneRebalanceIndex_eq]
  by_cases hlt : zoneShiftIndex dir (D.2 t) < D.1
  · have hlt' : zoneRebalanceIndex dir t D < D.1 := by rwa [zoneRebalanceIndex_eq]
    rw [zoneTrackStepData_of_lt dir t hlt', zoneRebalanceData_eq]
    simp only [if_pos hlt, Function.update_self]
    refine ⟨fun n hn hj => (hreb _ (hD t) hlt n hn).1 hj,
      fun n hn hj => (hreb _ (hD t) hlt n hn).2 hj, ?_, fun t' ht' => ?_, trivial⟩
    · rw [(hreb _ (hD t) hlt D.1 le_rfl).2 hlt, add_zero]
    · rw [Function.update_of_ne ht', add_zero]
      exact ⟨fun _ _ => rfl, rfl⟩
  · have hlt' : ¬ zoneRebalanceIndex dir t D < D.1 := by rwa [zoneRebalanceIndex_eq]
    have hidx : zoneShiftIndex dir (D.2 t) = D.1 :=
      eq_of_le_of_not_lt (zoneShiftIndex_le dir (D.2 t)) hlt
    have hidx' := zoneShiftIndex_extend dir (D.2 t) hidx
    have hfull' := tt_full_extend _ (hD t)
    have hlt₂ : zoneShiftIndex dir (D.2 t).extend < D.1 + 1 := by
      rw [hidx']
      exact Nat.lt_succ_self _
    rw [zoneTrackStepData_of_not_lt dir t hlt', zoneRebalanceData_eq, zoneExtendData_eq]
    simp only [if_neg hlt, Function.update_self]
    refine ⟨fun n hn _ => (hreb _ hfull' hlt₂ n (by omega)).1 (by rw [hidx']; exact hn),
      fun n hn hj => absurd hj (by rw [hidx]; omega), ?_, fun t' ht' => ?_, trivial⟩
    · rw [(hreb _ hfull' hlt₂ (D.1 + 1) le_rfl).2 (by rw [hidx']; exact Nat.lt_succ_self _),
        (tt_rsum_extend (D.2 t)).2]
      push_cast
      ring
    · rw [Function.update_of_ne ht']
      exact ⟨fun n hn => (tt_rsum_extend (D.2 t')).1 n hn, (tt_rsum_extend (D.2 t')).2⟩

/-! ### Side totals through a round -/

/-- The tracks' steps never lower the level count. -/
private theorem tt_Dtr_level_mono {k : ℕ} (m : Fin k → SignType) (H : ZoneData k) (j₁ : ℕ) :
    ∀ j₂, j₁ ≤ j₂ → (tt_Dtr m H j₁).1 ≤ (tt_Dtr m H j₂).1 := by
  refine fun j₂ hj => monotone_nat_of_le_succ (f := fun j => (tt_Dtr m H j).1) (fun j => ?_) hj
  show (tt_Dtr m H j).1 ≤ (tt_Dtr m H (j + 1)).1
  by_cases h : j < k
  · rw [show tt_Dtr m H (j + 1) = tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) from dif_pos h]
    by_cases h0 : m ⟨j, h⟩ = 0
    · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) = tt_Dtr m H j from if_pos h0]
    · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) =
        zoneTrackStepData (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩ (tt_Dtr m H j) from if_neg h0]
      by_cases hlt : zoneRebalanceIndex (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩ (tt_Dtr m H j) <
          (tt_Dtr m H j).1
      · rw [zoneTrackStepData_of_lt _ _ hlt, zoneRebalanceData_eq]
      · rw [zoneTrackStepData_of_not_lt _ _ hlt, zoneRebalanceData_eq, zoneExtendData_eq]
        exact Nat.le_succ _
  · rw [show tt_Dtr m H (j + 1) = tt_Dtr m H j from dif_neg h]

/-- **The other tracks' steps keep a track's side totals** below a laid-out level `n`: from
`j₁` to `j₂` the steps of tracks other than `t` change no side total of track `t` below `n`. -/
private theorem tt_Dtr_other {k : ℕ} (m : Fin k → SignType) (H : ZoneData k) (hH : tt_fullD H)
    (t : Fin k) (n j₁ : ℕ) (hn : n ≤ (tt_Dtr m H j₁).1) :
    ∀ j₂, j₁ ≤ j₂ → (t.val < j₁ ∨ j₂ ≤ t.val) →
      tt_rsum ((tt_Dtr m H j₂).2 t) n = tt_rsum ((tt_Dtr m H j₁).2 t) n := by
  intro j₂ hj
  induction j₂, hj using Nat.le_induction with
  | base => exact fun _ => rfl
  | succ j hj ih =>
    intro hc
    rw [← ih (by omega)]
    have hlev := tt_Dtr_level_mono m H j₁ j hj
    by_cases h : j < k
    · rw [show tt_Dtr m H (j + 1) = tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) from dif_pos h]
      by_cases h0 : m ⟨j, h⟩ = 0
      · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) = tt_Dtr m H j from if_pos h0]
      · rw [show tt_trackData (m ⟨j, h⟩) ⟨j, h⟩ (tt_Dtr m H j) =
          zoneTrackStepData (tt_dir (m ⟨j, h⟩)) ⟨j, h⟩ (tt_Dtr m H j) from if_neg h0]
        have ht : t ≠ ⟨j, h⟩ := fun he => by rw [he] at hc; simp at hc; omega
        exact ((tt_trackStep_rsum _ _ _ (tt_Dtr_inv m H hH j).1).2.2.2.1 t ht).1 n (by omega)
    · rw [show tt_Dtr m H (j + 1) = tt_Dtr m H j from dif_neg h]

/-- The scanned index of track `t`'s step in the round with action `a` from data `D`. -/
private def tt_idxA {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k) (t : Fin k) : ℕ :=
  tt_idx (tt_moves a t) t (tt_Dtr (tt_moves a) (tt_homeData a D) t.val)

/-- Track `t`'s own step in a round: the data after it are its step from the data before. -/
private theorem tt_Dtr_own {k : ℕ} (m : Fin k → SignType) (H : ZoneData k) (t : Fin k) :
    tt_Dtr m H (t.val + 1) = tt_trackData (m t) t (tt_Dtr m H t.val) :=
  dif_pos t.isLt

/-- **One round on track `t`'s side totals below a level `n ≥ 1`** [AB09, §1.7]. With `D` full,
the round's action `a`, its data `D'` and track `t`'s scanned index `i₀`:
* if `n ≤ i₀`, then `D'` has its levels below `n` laid out and half full on track `t`: the side
  total below `n` is `2^n − 1`;
* if `n ≤ D.1` and `n ≤ i₀`, the side total below `n` before the round is `0` or `2^{n+1} − 2`;
* if `n ≤ D.1` and `i₀ < n`, the round changes it by at most one;
* the level count never drops, and bounds `i₀` after the round.

**Proof sketch.** The home write and the other tracks' steps keep track `t`'s side totals below
a laid-out level (`tt_rsum_homeWrite`, `tt_Dtr_other`); track `t`'s own step is
`tt_trackStep_rsum` (a stay changes nothing and has index `0`), and the scanned zones below a
large index are empty or full (`tt_rsum_low`). -/
private theorem tt_round_rsum {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k)
    (hD : tt_fullD D) (t : Fin k) (n : ℕ) (hn1 : 1 ≤ n) :
    (n ≤ tt_idxA a D t → tt_rsum ((tt_roundData a D).2 t) n = 2 ^ n - 1 ∧
      n ≤ (tt_roundData a D).1) ∧
    (n ≤ D.1 → n ≤ tt_idxA a D t →
      tt_rsum (D.2 t) n = 0 ∨ tt_rsum (D.2 t) n = 2 ^ (n + 1) - 2) ∧
    (n ≤ D.1 → tt_idxA a D t < n →
      (tt_rsum ((tt_roundData a D).2 t) n : ℤ) ≤ tt_rsum (D.2 t) n + 1 ∧
        (tt_rsum (D.2 t) n : ℤ) ≤ tt_rsum ((tt_roundData a D).2 t) n + 1) ∧
    D.1 ≤ (tt_roundData a D).1 ∧ tt_idxA a D t ≤ (tt_roundData a D).1 := by
  set m := tt_moves a with hm
  set H := tt_homeData a D with hH
  have hHf : tt_fullD H := (tt_homeData_inv a D hD).1
  have hH1 : H.1 = D.1 := rfl
  have hHr : ∀ n, tt_rsum (H.2 t) n = tt_rsum (D.2 t) n := fun n => tt_rsum_homeWrite _ _ n
  set E := tt_Dtr m H t.val with hE
  have hEf : tt_fullD E := (tt_Dtr_inv m H hHf t.val).1
  have hEl : D.1 ≤ E.1 := tt_Dtr_level_mono m H 0 t.val (Nat.zero_le _)
  have hE'l : E.1 ≤ (tt_Dtr m H (t.val + 1)).1 := tt_Dtr_level_mono m H _ _ (Nat.le_succ _)
  have hDl : (tt_Dtr m H (t.val + 1)).1 ≤ (tt_roundData a D).1 :=
    tt_Dtr_level_mono m H _ k t.isLt
  have hEr : n ≤ D.1 → tt_rsum (E.2 t) n = tt_rsum (D.2 t) n := fun hnD => by
    rw [hE, tt_Dtr_other m H hHf t n 0 hnD t.val (Nat.zero_le _) (Or.inr le_rfl)]
    exact hHr n
  have hD'r : n ≤ (tt_Dtr m H (t.val + 1)).1 → tt_rsum ((tt_roundData a D).2 t) n =
      tt_rsum ((tt_Dtr m H (t.val + 1)).2 t) n := fun hn =>
    tt_Dtr_other m H hHf t n (t.val + 1) hn k t.isLt (Or.inl (Nat.lt_succ_self _))
  have hown := tt_Dtr_own m H t
  have hidx : tt_idxA a D t = tt_idx (m t) t E := rfl
  by_cases h0 : m t = 0
  · have hi0 : tt_idxA a D t = 0 := by rw [hidx]; exact if_pos h0
    rw [show tt_trackData (m t) t E = E from if_pos h0] at hown
    refine ⟨fun h => absurd h (by omega), fun _ h => absurd h (by omega), fun hnD _ => ?_,
      by rw [← hH1]; exact hEl.trans (hE'l.trans hDl), by rw [hi0]; exact Nat.zero_le _⟩
    rw [hD'r (by rw [hown]; omega), hown, hEr hnD]
    constructor <;> omega
  · set dir := tt_dir (m t)
    have hi : tt_idxA a D t = zoneRebalanceIndex dir t E := by rw [hidx]; exact if_neg h0
    rw [show tt_trackData (m t) t E = zoneTrackStepData dir t E from if_neg h0] at hown
    obtain ⟨c1, c2, -, -, -⟩ := tt_trackStep_rsum dir t E hEf
    have hiE : zoneRebalanceIndex dir t E ≤ E.1 := zoneRebalanceIndex_le dir t E
    refine ⟨fun hni => ?_, fun hnD hni => ?_, fun hnD hni => ?_,
      by rw [← hH1]; exact hEl.trans (hE'l.trans hDl), ?_⟩
    · rw [hi] at hni
      have hlev : n ≤ (tt_Dtr m H (t.val + 1)).1 := (hni.trans hiE).trans hE'l
      refine ⟨?_, hlev.trans hDl⟩
      rw [hD'r hlev, hown]
      exact c1 n (hni.trans hiE) hni
    · rw [← hEr hnD]
      rw [hi, zoneRebalanceIndex_eq] at hni
      have hl := tt_rsum_low dir (E.2 t) (hEf t) n hni (by omega)
      cases hdir : dir
      · rw [hdir, if_neg (by simp)] at hl
        exact Or.inr hl
      · rw [hdir, if_pos rfl] at hl
        exact Or.inl hl
    · rw [hi] at hni
      have hlev : n ≤ (tt_Dtr m H (t.val + 1)).1 := by omega
      rw [hD'r hlev, hown, c2 n (by omega) hni, hEr hnD]
      have : tt_shift dir = 1 ∨ tt_shift dir = -1 := by cases dir <;> simp [tt_shift]
      rcases this with hs | hs <;> rw [hs] <;> constructor <;> omega
    · rw [hi]
      exact hiE.trans (hE'l.trans hDl)

/-! ### Counting the expensive steps -/

/-- **Sparse sets of times are small**: a set of times below `T` any two of which are at least
`g ≥ 1` apart has at most `T / g + 1` elements.

**Proof sketch.** Division by `g` is injective on the set, since two of its elements differ by
at least `g`, and maps it into `{0, …, T / g}`. -/
private theorem tt_card_le_of_gap (T g : ℕ) (hg : 0 < g) (S : Finset ℕ)
    (hS : ∀ a ∈ S, a < T) (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → a + g ≤ b) :
    S.card ≤ T / g + 1 := by
  have hstep : ∀ a ∈ S, ∀ b ∈ S, a < b → a / g < b / g := by
    intro a ha b hb hab
    have h := hgap a ha b hb hab
    calc a / g < a / g + 1 := Nat.lt_succ_self _
      _ = (a + g) / g := (Nat.add_div_right a hg).symm
      _ ≤ b / g := Nat.div_le_div_right h
  have hinj : Set.InjOn (fun a => a / g) S := StrictMonoOn.injOn hstep
  calc S.card ≤ (Finset.range (T / g + 1)).card :=
        Finset.card_le_card_of_injOn (fun a => a / g) (fun a ha =>
          Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (hS a ha).le))) hinj
    _ = T / g + 1 := Finset.card_range _

/-! ### The count and level bounds over the run -/

/-- The scanned index of track `t`'s step in round `r` of the simulation of `M` on `x`
(`0` once `M` has halted). -/
private def tt_idxR (M : FinTM Bool) (x : List Bool) (t : Fin M.k) (r : ℕ) : ℕ :=
  match (tt_c M x r).state with
  | some q => tt_idxA (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r) t
  | none => 0

/-- **Track `t`'s side totals below `n ≥ 1` over one round of the run**: `tt_round_rsum` at a
live time. -/
private theorem tt_orbit_rsum (M : FinTM Bool) (x : List Bool) (r : ℕ)
    (hr : (tt_c M x r).state ≠ none) (t : Fin M.k) (n : ℕ) (hn1 : 1 ≤ n) :
    (n ≤ tt_idxR M x t r → tt_rsum ((tt_D M x (r + 1)).2 t) n = 2 ^ n - 1 ∧
      n ≤ (tt_D M x (r + 1)).1) ∧
    (n ≤ (tt_D M x r).1 → n ≤ tt_idxR M x t r →
      tt_rsum ((tt_D M x r).2 t) n = 0 ∨ tt_rsum ((tt_D M x r).2 t) n = 2 ^ (n + 1) - 2) ∧
    (n ≤ (tt_D M x r).1 → tt_idxR M x t r < n →
      (tt_rsum ((tt_D M x (r + 1)).2 t) n : ℤ) ≤ tt_rsum ((tt_D M x r).2 t) n + 1 ∧
        (tt_rsum ((tt_D M x r).2 t) n : ℤ) ≤ tt_rsum ((tt_D M x (r + 1)).2 t) n + 1) ∧
    (tt_D M x r).1 ≤ (tt_D M x (r + 1)).1 ∧ tt_idxR M x t r ≤ (tt_D M x (r + 1)).1 := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hr
  have hidx : tt_idxR M x t r =
      tt_idxA (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r)) (tt_D M x r) t := by
    show (match (tt_c M x r).state with
      | some q => _
      | none => 0) = _
    rw [hq]
  rw [tt_D_succ M x r q hq, hidx]
  exact tt_round_rsum _ _ (tt_D_inv M x r).1 t n hn1

/-- **The count hypothesis** [AB09, §1.7; the book's amortization]: in a run of `T` live
rounds, track `t`'s steps of scanned index above `i` number at most `T / 2^i + 1`.

**Proof sketch.** After such a step the levels `0, …, i` of track `t` are half full: its side
total below `i + 1` is `2^{i+1} − 1` (`tt_orbit_rsum`). Each later round changes it by at most
one, or resets it to `2^{i+1} − 1` after another such step; and such a step needs it to be `0`
or `2^{i+2} − 2`. So two such steps are at least `2^{i+1} − 1 ≥ 2^i` rounds apart, and
`tt_card_le_of_gap` counts them with the gap `2^i`. -/
private theorem tt_count (M : FinTM Bool) (x : List Bool) (T : ℕ)
    (hT : ∀ r < T, (tt_c M x r).state ≠ none) (t : Fin M.k) (i : ℕ) :
    ((Finset.range T).filter (fun s => i < tt_idxR M x t s)).card ≤ T / 2 ^ i + 1 := by
  set n := i + 1 with hn
  have hn1 : 1 ≤ n := Nat.le_add_left 1 i
  refine tt_card_le_of_gap T (2 ^ i) (Nat.two_pow_pos i) _
    (fun a ha => Finset.mem_range.mp (Finset.mem_filter.mp ha).1) fun a ha b hb hab => ?_
  obtain ⟨haT, hai⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbT, hbi⟩ := Finset.mem_filter.mp hb
  rw [Finset.mem_range] at haT hbT
  have F := fun r (hr : r < T) => tt_orbit_rsum M x r (hT r hr) t n hn1
  obtain ⟨hVa, hla⟩ := (F a haT).1 hai
  -- the levels below `n` stay laid out after round `a`
  have hlev : ∀ r, a + 1 ≤ r → r ≤ b → n ≤ (tt_D M x r).1 := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => exact fun _ => hla
    | succ r hr ih => exact fun hrb => (ih (by omega)).trans (F r (by omega)).2.2.2.1
  -- the side total drifts by at most one per round
  have hdrift : ∀ r, a + 1 ≤ r → r ≤ b →
      ((tt_rsum ((tt_D M x r).2 t) n : ℤ) - (2 ^ n - 1) ≤ r - (a + 1) ∧
        ((2 ^ n - 1 : ℤ) - tt_rsum ((tt_D M x r).2 t) n ≤ r - (a + 1))) := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base =>
      intro _
      rw [hVa]
      have := Nat.one_le_two_pow (n := n)
      push_cast [Nat.cast_sub this]
      constructor <;> omega
    | succ r hr ih =>
      intro hrb
      obtain ⟨ih₁, ih₂⟩ := ih (by omega)
      by_cases hbig : n ≤ tt_idxR M x t r
      · rw [((F r (by omega)).1 hbig).1]
        have := Nat.one_le_two_pow (n := n)
        push_cast [Nat.cast_sub this]
        constructor <;> omega
      · obtain ⟨d₁, d₂⟩ := (F r (by omega)).2.2.1 (hlev r hr (by omega)) (by omega)
        push_cast
        constructor <;> omega
  obtain ⟨e₁, e₂⟩ := hdrift b (by omega) le_rfl
  have hb := (F b hbT).2.1 (hlev b (by omega) le_rfl) hbi
  have h2 : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
  have hpow : 2 ^ n = 2 * 2 ^ i := by rw [hn, pow_succ']
  rcases hb with hb | hb
  · rw [hb] at e₂
    push_cast at e₂
    have : (2 : ℤ) ^ n = 2 * 2 ^ i := by exact_mod_cast hpow
    have : (1 : ℤ) ≤ 2 ^ i := by exact_mod_cast Nat.one_le_two_pow
    have key : (a : ℤ) + 2 ^ i ≤ b := by omega
    exact_mod_cast key
  · rw [hb] at e₁
    have h4 : 2 ≤ 2 ^ (n + 1) := Nat.le_self_pow (by omega) 2
    push_cast [Nat.cast_sub h4] at e₁
    have : (2 : ℤ) ^ n = 2 * 2 ^ i := by exact_mod_cast hpow
    have : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := pow_succ' 2 n
    have : (1 : ℤ) ≤ 2 ^ i := by exact_mod_cast Nat.one_le_two_pow
    have key : (a : ℤ) + 2 ^ i ≤ b := by omega
    exact_mod_cast key

/-- **The displacement invariant through a round** [AB09, §1.7]. If every track's whole side
total plus its head's displacement `pos t` is `2^{D.1} − 1`, and every displacement is at most
`r`, then after the round with action `a` the same holds with the displacements moved by the
heads' moves, and the level count `ℓ'` satisfies `2^{ℓ'} ≤ max (2^{D.1}) (2 (r + 1))`: an
extension at level `ℓ` needs every feeding zone empty, so a displacement of `2^ℓ − 1`.

**Proof sketch.** Induction over the round's tracks. A move changes its track's side total by
the opposite of its displacement (`tt_trackStep_rsum`, `tt_shift_dir`), and an extension adds
`2^ℓ` to every track's side total and to `2^ℓ − 1`. A short scan has an extreme side total
(`tt_rsum_low`: `0` or `2^{ℓ+1} − 2`), so `|pos t| = 2^ℓ − 1 ≤ r`. -/
private theorem tt_round_disp {k : ℕ} {S : Type} (a : Action k Bool S) (D : ZoneData k)
    (hD : tt_fullD D) (pos : Fin k → ℤ) (r : ℕ)
    (hQ : ∀ t, (tt_rsum (D.2 t) D.1 : ℤ) + pos t = 2 ^ D.1 - 1) (hpos : ∀ t, |pos t| ≤ r) :
    (∀ t, (tt_rsum ((tt_roundData a D).2 t) (tt_roundData a D).1 : ℤ) +
      (pos t + (tt_moves a t : ℤ)) = 2 ^ (tt_roundData a D).1 - 1) ∧
    2 ^ (tt_roundData a D).1 ≤ max (2 ^ D.1) (2 * (r + 1)) := by
  set m := tt_moves a
  set H := tt_homeData a D
  have hHf : tt_fullD H := (tt_homeData_inv a D hD).1
  have key : ∀ j, (∀ t, (tt_rsum ((tt_Dtr m H j).2 t) (tt_Dtr m H j).1 : ℤ) + pos t +
      (if t.val < j then (m t : ℤ) else 0) = 2 ^ (tt_Dtr m H j).1 - 1) ∧
      2 ^ (tt_Dtr m H j).1 ≤ max (2 ^ D.1) (2 * (r + 1)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun t => ?_, le_max_left _ _⟩
      rw [if_neg (Nat.not_lt_zero _), add_zero]
      show (tt_rsum (zoneHomeWrite (D.2 t) _) D.1 : ℤ) + pos t = 2 ^ D.1 - 1
      rw [tt_rsum_homeWrite]
      exact hQ t
    | succ j ih =>
      obtain ⟨ih₁, ih₂⟩ := ih
      by_cases hj : j < k
      · rw [show tt_Dtr m H (j + 1) = tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ (tt_Dtr m H j)
          from dif_pos hj]
        set E := tt_Dtr m H j
        have hEf : tt_fullD E := (tt_Dtr_inv m H hHf j).1
        by_cases h0 : m ⟨j, hj⟩ = 0
        · rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ E = E from if_pos h0]
          refine ⟨fun t => ?_, ih₂⟩
          rw [← ih₁ t]
          by_cases ht : t = ⟨j, hj⟩
          · subst ht
            rw [if_pos (Nat.lt_succ_self j), if_neg (lt_irrefl j), h0]
            simp
          · have : t.val ≠ j := Fin.val_ne_of_ne ht
            by_cases htj : t.val < j
            · rw [if_pos htj, if_pos (by omega)]
            · rw [if_neg htj, if_neg (by omega)]
        · set dir := tt_dir (m ⟨j, hj⟩)
          rw [show tt_trackData (m ⟨j, hj⟩) ⟨j, hj⟩ E = zoneTrackStepData dir ⟨j, hj⟩ E
            from if_neg h0]
          obtain ⟨-, -, c3, c4, c5⟩ := tt_trackStep_rsum dir ⟨j, hj⟩ E hEf
          have hsh : tt_shift dir = (m ⟨j, hj⟩ : ℤ) := tt_shift_dir _ h0
          have hℓ : (2 : ℤ) ^ (zoneTrackStepData dir ⟨j, hj⟩ E).1 = 2 ^ E.1 +
              (if zoneRebalanceIndex dir ⟨j, hj⟩ E < E.1 then 0 else 2 ^ E.1) := by
            rw [c5]
            split_ifs
            · ring
            · ring
          refine ⟨fun t => ?_, ?_⟩
          · by_cases ht : t = ⟨j, hj⟩
            · subst ht
              rw [c3, hℓ, if_pos (Nat.lt_succ_self j), ← hsh]
              have := ih₁ ⟨j, hj⟩
              rw [if_neg (lt_irrefl j), add_zero] at this
              linarith
            · have : t.val ≠ j := Fin.val_ne_of_ne ht
              obtain ⟨-, c4'⟩ := c4 t ht
              rw [c4', hℓ]
              have := ih₁ t
              have hif : (if t.val < j + 1 then (m t : ℤ) else 0) =
                  (if t.val < j then (m t : ℤ) else 0) := by
                by_cases htj : t.val < j
                · rw [if_pos htj, if_pos (by omega)]
                · rw [if_neg htj, if_neg (by omega)]
              rw [hif]
              push_cast
              linarith
          · rw [c5]
            split_ifs with hlt
            · exact ih₂
            · -- an extension at level `E.1`: the scanned side is extreme
              have hidx : zoneShiftIndex dir (E.2 ⟨j, hj⟩) = E.1 := by
                rw [← zoneRebalanceIndex_eq]
                exact eq_of_le_of_not_lt (zoneRebalanceIndex_le _ _ _) hlt
              have hl := tt_rsum_low dir (E.2 ⟨j, hj⟩) (hEf _) E.1 hidx.ge le_rfl
              have hq := ih₁ ⟨j, hj⟩
              rw [if_neg (lt_irrefl j), add_zero] at hq
              have hp := abs_le.mp (hpos ⟨j, hj⟩)
              have h2 : 2 ≤ 2 ^ (E.1 + 1) := Nat.le_self_pow (by omega) 2
              have hb : 2 ^ E.1 ≤ r + 1 := by
                cases hdir : dir
                · rw [hdir, if_neg (by simp)] at hl
                  rw [hl] at hq
                  push_cast [Nat.cast_sub h2] at hq
                  have : (2 : ℤ) ^ (E.1 + 1) = 2 * 2 ^ E.1 := pow_succ' 2 E.1
                  have : (2 : ℤ) ^ E.1 ≤ r + 1 := by linarith
                  exact_mod_cast this
                · rw [hdir, if_pos rfl] at hl
                  rw [hl] at hq
                  push_cast at hq
                  have : (2 : ℤ) ^ E.1 ≤ r + 1 := by linarith
                  exact_mod_cast this
              rw [pow_succ]
              exact le_max_of_le_right (by omega)
      · rw [show tt_Dtr m H (j + 1) = tt_Dtr m H j from dif_neg hj]
        refine ⟨fun t => ?_, ih₂⟩
        rw [← ih₁ t, if_pos (by omega), if_pos (by omega)]
  obtain ⟨k₁, k₂⟩ := key k
  refine ⟨fun t => ?_, k₂⟩
  have := k₁ t
  rw [if_pos t.isLt] at this
  rw [← add_assoc]
  exact this

/-- **The displacement invariant and the level bound along the run** [AB09, §1.7]: after `r`
steps every track's whole side total plus `M`'s head position is `2^{ℓ} − 1` for the level count
`ℓ`, and `2^ℓ ≤ 2 r + 1`.

**Proof sketch.** Induction on `r`: no level and heads at `0` at first; a live step is
`tt_round_disp` with the heads' moves (`Turing.Action.apply_workTapePos`) and `M`'s head bound
(`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`); a halted step changes nothing. -/
private theorem tt_D_level (M : FinTM Bool) (x : List Bool) (r : ℕ) :
    (∀ t, (tt_rsum ((tt_D M x r).2 t) (tt_D M x r).1 : ℤ) + (tt_c M x r).workTapePos t =
      2 ^ (tt_D M x r).1 - 1) ∧ 2 ^ (tt_D M x r).1 ≤ 2 * r + 1 := by
  induction r with
  | zero =>
    refine ⟨fun t => ?_, le_rfl⟩
    show (tt_rsum (ZoneContents.empty 0) 0 : ℤ) + (M.tm.runFrom (M.tm.initCfg x) 0).workTapePos t =
      2 ^ 0 - 1
    rw [MultiTapeTM.runFrom_zero, MultiTapeTM.initCfg_eq, Cfg.init_workTapePos]
    rfl
  | succ r ih =>
    obtain ⟨ih₁, ih₂⟩ := ih
    have hc : tt_c M x (r + 1) = M.tm.step (tt_c M x r) := MultiTapeTM.runFrom_succ_eq_step'
    cases hq : (tt_c M x r).state with
    | none =>
      have hD : tt_D M x (r + 1) = tt_D M x r := by
        show (match (tt_c M x r).state with
          | some q => _
          | none => tt_D M x r) = _
        rw [hq]
      rw [hD, hc, MultiTapeTM.step_of_halt hq]
      exact ⟨ih₁, by omega⟩
    | some q =>
      obtain ⟨hact, -, -⟩ := tt_round_inv M (tt_c M x r) q hq _ (tt_D_inv M x r).1
        (tt_D_inv M x r).2
      have hpos : ∀ t, |(tt_c M x r).workTapePos t| ≤ r := fun t => by
        have h : (tt_c M x r).workTapePos t ∈ Finset.Icc ((M.tm.initCfg x).workTapePos t - r)
            ((M.tm.initCfg x).workTapePos t + r) :=
          MultiTapeTM.workTapePos_runFrom_mem_Icc M.tm (M.tm.initCfg x) r t
        rw [MultiTapeTM.initCfg_eq, Cfg.init_workTapePos, Finset.mem_Icc] at h
        exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
      obtain ⟨d₁, d₂⟩ := tt_round_disp (tt_act M q (tt_c M x r).inputSymbol (tt_D M x r))
        (tt_D M x r) (tt_D_inv M x r).1 _ r ih₁ hpos
      rw [tt_D_succ M x r q hq]
      refine ⟨fun t => ?_, d₂.trans (max_le (by omega) (by omega))⟩
      rw [hc, MultiTapeTM.step_of_some hq, Action.apply_workTapePos, ← hact]
      exact d₁ t

/-- **The level bound** [AB09, §1.7]: in a run of `T` live rounds every scanned index is at most
`log₂ T + 1`.

**Proof sketch.** The index of round `s` is at most the level count after it (`tt_orbit_rsum`),
whose power of two is at most `2 (s + 1) + 1 ≤ 2 T + 1 < 2^{log₂ T + 2}` (`tt_D_level`,
`Nat.lt_pow_succ_log_self`). -/
private theorem tt_idxR_le (M : FinTM Bool) (x : List Bool) (T : ℕ)
    (hT : ∀ r < T, (tt_c M x r).state ≠ none) (t : Fin M.k) :
    ∀ s < T, tt_idxR M x t s ≤ Nat.log 2 T + 1 := by
  intro s hs
  have h1 := (tt_orbit_rsum M x s (hT s hs) t 1 le_rfl).2.2.2.2
  have h2 := (tt_D_level M x (s + 1)).2
  have h3 := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) T
  refine h1.trans ?_
  by_contra hc
  have h4 : 2 ^ (Nat.log 2 T + 2) ≤ 2 ^ (tt_D M x (s + 1)).1 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ] at h4
  omega

/-! ### The cost -/

/-- **The cost of a halting run** [AB09, §1.7]: if `M` is live for its first `t₀ ≥ 1` steps, the
zone machine's time `∑_{r < t₀ − 1} T_r + 1` is at most
`(2 + k (5 A + 1)) · (t₀ + 1)(log₂(t₀ + 1) + 1)`.

**Proof sketch.** The time is at most the sum of all `t₀` rounds' lengths (the last round takes
at least one step, `tt_T_ge`). Each round costs at most `2 + A ∑_t (2^{i₀} + 1) + k`
(`tt_τ_le`), so `Turing.sum_cost_le_of_count` applies with `B = 2`, the count hypothesis
`tt_count` and the level bound `L = log₂ t₀ + 1` (`tt_idxR_le`), giving
`2 t₀ + k (A ((L + 2) t₀ + 2^L) + t₀)`; then `2^L ≤ 2 t₀` (`Nat.pow_log_le_self`) and
`log₂ t₀ ≤ log₂ (t₀ + 1)` (`Nat.log_mono_right`). -/
private theorem tt_cost (M : FinTM Bool) {A : ℕ} (F : tt_Fam M.k A) (hk : 0 < M.k)
    (x : List Bool) (t₀ : ℕ) (h1 : 1 ≤ t₀) (hl : ∀ r < t₀, (tt_c M x r).state ≠ none) :
    ∑ r ∈ Finset.range (t₀ - 1), tt_T M F x r + 1 ≤
      (2 + M.k * (5 * A + 1)) * ((t₀ + 1) * (Nat.log 2 (t₀ + 1) + 1)) := by
  set L := Nat.log 2 t₀ + 1 with hL
  -- the time is at most the sum of all the rounds
  have hsum : ∑ r ∈ Finset.range (t₀ - 1), tt_T M F x r + 1 ≤
      ∑ r ∈ Finset.range t₀, tt_T M F x r := by
    obtain ⟨s, rfl⟩ : ∃ s, t₀ = s + 1 := Nat.exists_eq_add_one.mpr h1
    rw [Nat.add_sub_cancel, Finset.sum_range_succ]
    have := tt_T_ge M F x s (hl s (by omega))
    omega
  -- each round's cost
  have hstep : ∀ s < t₀, tt_T M F x s ≤
      2 + A * ∑ t, (2 ^ tt_idxR M x t s + 1) + M.k := by
    intro s hs
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hl s hs)
    have hT : tt_T M F x s = 2 + ∑ j ∈ Finset.range M.k, tt_τ M F (x.map Sum.inl)
        (tt_moves (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)))
        (tt_homeData (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s))
        (moveInputPos (tt_ipOf M (tt_c M x s))
          (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).inputTape)
        ((tt_c M x s).output.map Sum.inl ++
          ((tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).output.map Sum.inl).toList) j := by
      show (match (tt_c M x s).state with
        | some q => _
        | none => 0) = _
      rw [hq]
    have hidx : ∀ t, tt_idxR M x t s =
        tt_idxA (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s) t := by
      intro t
      show (match (tt_c M x s).state with
        | some q => _
        | none => 0) = _
      rw [hq]
    rw [hT]
    have hle : ∀ j : Fin M.k, tt_τ M F (x.map Sum.inl)
        (tt_moves (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)))
        (tt_homeData (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s))
        (moveInputPos (tt_ipOf M (tt_c M x s))
          (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).inputTape)
        ((tt_c M x s).output.map Sum.inl ++
          ((tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).output.map Sum.inl).toList) j ≤
        A * (2 ^ tt_idxR M x j s + 1) + 1 := by
      intro j
      rw [hidx]
      exact tt_τ_le M F hk _ _ _ _ _ j.val j.isLt
    have hsumτ := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hle j
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsumτ
    simp only [Finset.sum_const, Finset.card_fin, Nat.nsmul_eq_mul, mul_one] at hsumτ
    rw [← Fin.sum_univ_eq_sum_range (fun j => tt_τ M F (x.map Sum.inl)
        (tt_moves (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)))
        (tt_homeData (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)) (tt_D M x s))
        (moveInputPos (tt_ipOf M (tt_c M x s))
          (tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).inputTape)
        ((tt_c M x s).output.map Sum.inl ++
          ((tt_act M q (tt_c M x s).inputSymbol (tt_D M x s)).output.map Sum.inl).toList) j) M.k]
    omega
  have hcost := sum_cost_le_of_count M.k t₀ L A 2 (fun t s => tt_idxR M x t s) (tt_T M F x)
    hstep (fun t => tt_idxR_le M x t₀ hl t) (fun t i _ => tt_count M x t₀ hl t i)
  -- the arithmetic
  have hpow : 2 ^ L ≤ 2 * t₀ := by
    rw [hL, pow_succ]
    have := Nat.pow_log_le_self 2 (show t₀ ≠ 0 by omega)
    omega
  have hlog : Nat.log 2 t₀ ≤ Nat.log 2 (t₀ + 1) := Nat.log_mono_right (Nat.le_succ t₀)
  set lg := Nat.log 2 (t₀ + 1)
  have hP : t₀ ≤ (t₀ + 1) * (lg + 1) := by nlinarith
  have hL3 : (L + 2) * t₀ ≤ 3 * ((t₀ + 1) * (lg + 1)) := by nlinarith
  refine hsum.trans (hcost.trans ?_)
  have e1 : 2 * t₀ ≤ 2 * ((t₀ + 1) * (lg + 1)) := by omega
  have e2 : M.k * (A * ((L + 2) * t₀ + 2 ^ L) + t₀) ≤
      M.k * (5 * A + 1) * ((t₀ + 1) * (lg + 1)) := by
    have : A * ((L + 2) * t₀ + 2 ^ L) + t₀ ≤ (5 * A + 1) * ((t₀ + 1) * (lg + 1)) := by
      nlinarith
    calc M.k * (A * ((L + 2) * t₀ + 2 ^ L) + t₀) ≤ M.k * ((5 * A + 1) * ((t₀ + 1) * (lg + 1))) :=
          Nat.mul_le_mul_left _ this
      _ = M.k * (5 * A + 1) * ((t₀ + 1) * (lg + 1)) := by ring
  nlinarith

/-! ### The target -/

/-- **Two work tapes suffice, run by run** [HS66]: every binary machine `M` has a binary
equivalent `M'` with two work tapes that reproduces each halting run of `M` of `t` steps within
`c · (t + 1)(log₂(t + 1) + 1)` steps, and every completed output of `M'` is an output of `M` on
the same input.

**Proof sketch.** (The Hennie–Stearns simulation.) The first work tape of `M'` holds all `k` of
`M`'s work tapes as tracks, folded around a fixed origin cell into zones of doubling sizes
`2^i`, so that every simulated head stays at the origin and a tape movement shifts contents
between neighbouring zones. Each side of a level is empty, half full or full, and the two sides
of a level together always hold the same number of cells. A shift that empties or fills a zone `i`
rebalances zones `0, …, i` using the second work tape as scratch, in `O(2^i)` steps, restoring
every level below `i` to half full, and a zone `i` is rebalanced at most once every `2^(i-1)`
simulated steps. Summing over the zones
`0, …, log₂ t + 1` that a run of `t` steps can rebalance gives `O(t log t)` steps in all. The
converse holds because `M'` writes an output symbol exactly when `M` does, in the same order, and
halts only when `M` halts. With no work tapes, `M` is run directly beside two idle tapes. -/
theorem two_work_tapes_run (M : FinTM Bool) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      (∀ (x output : List Bool) (t : ℕ), M.ComputesInTime x output t →
        M'.ComputesInTime x output (c * ((t + 1) * (Nat.log 2 (t + 1) + 1)))) ∧
      ∀ (x output : List Bool), (∃ t, M'.ComputesInTime x output t) →
        ∃ t, M.ComputesInTime x output t := by
  refine tt_route (fun M hk => ?_) M
  -- the track-step family, chosen once (`Turing.exists_zoneTrackStepTM`)
  obtain ⟨A, hA⟩ := exists_zoneTrackStepTM M.k
  choose S fin dec Mt entry X hnone hR using hA
  choose R hpre hspec using hR
  let F : tt_Fam M.k A := ⟨S, fin, dec, Mt, entry, X, hnone, R, hpre, hspec⟩
  refine ⟨tt_HS M F hk, rfl, 2 + M.k * (5 * A + 1), fun x o t h => ?_,
    fun x o' t' h => tt_converse M F hk x o' t' h⟩
  obtain ⟨t₀, ht₀, h1, hl, hHS⟩ := tt_forward_run M F hk x o t h
  refine hHS.mono ((tt_cost M F hk x t₀ h1 hl).trans (Nat.mul_le_mul_left _ ?_))
  exact Nat.mul_le_mul (by omega) (Nat.add_le_add_right (Nat.log_mono_right (by omega)) 1)

/-- **Two work tapes suffice** for computing a function: if a binary machine computes `f` within
time `T`, then a binary machine with two work tapes computes `f` within
`c · (T n + 1)(log₂(T n + 1) + 1)` for some constant `c` [HS66].

**Proof sketch.** Apply `Turing.FinTM.two_work_tapes_run` to `M` and use its forward direction at
each input `x`, with the run of `T |x|` steps that computes `f x`. -/
theorem two_work_tapes_binary (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    ∃ (M' : FinTM Bool) (c : ℕ), M'.k = 2 ∧
      M'.ComputesFunInTime f fun n => c * ((T n + 1) * (Nat.log 2 (T n + 1) + 1)) := by
  obtain ⟨M', c, hk, h, -⟩ := two_work_tapes_run M
  exact ⟨M', c, hk, (computesFunInTime_iff _ _ _).2 fun x =>
    h x (f x) _ ((computesFunInTime_iff _ _ _).1 hM x)⟩

end Turing.FinTM
```

## ===== TCSlib/Complexity/TuringMachine/Finite.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Data.Fintype.Basic
import TCSlib.Complexity.TuringMachine.Deterministic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bundled finite Turing machines

The raw model `Turing.MultiTapeTM k Symbol State` deliberately does not require `Symbol` or
`State` to be finite: semantics, simulations, and resource counting do not need it, and
compound state types arise freely in constructions. Finiteness is nevertheless
mathematically essential for complexity theory — with infinitely many states a machine can
memorize its whole input in the state and decide any language in linear time, and an
infinite transition table has no string encoding.

This file provides the bundled layer `Turing.FinTM`: a machine together with `Fintype` and
`DecidableEq` instances for its state type. All headline definitions of the Chapter 1
development (`DTIME`, `P`, machine encodings, the universal machine) are stated exclusively
over `FinTM`, so the finiteness hypothesis can never be dropped by accident. The instances
are carried as *data* (not `Finite` propositions) because the machine-encoding function
`⌞M⌟` must enumerate the transition table.

The alphabet parameter `Symbol` stays explicit and unbundled: the Chapter 1 headline
definitions fix `Symbol := Bool` (see `TCSlib.Complexity.ClassP.DTIME`), and results that
need a finite alphabet for a general `Symbol` take `[Fintype Symbol]` hypotheses at use
sites.

## Main definitions

* `Turing.FinTM Symbol` — a multi-tape TM over alphabet `Option Symbol` with a bundled
  finite state type. [AB09, §1.2]
* `Turing.FinTM.ComputesInTime` — the machine halts on `input` within `t` steps with
  `output` on the output tape (time-only variant of
  `Turing.MultiTapeTM.ComputesInTimeAndSpace`). [AB09, Definition 1.3]
* `Turing.FinTM.ComputesFunInTime` — the machine computes `f` in time `T`.
  [AB09, Definition 1.3]
* `Turing.FinTM.Computes` — the machine computes `f` with no time constraint; the
  notion of computability underlying the uncomputability results. [AB09, §1.4, p. 20]

## Main results

* `Turing.FinTM.ComputesInTime.mono` — halting is absorbing, so the time bound can be
  weakened.
* `Turing.FinTM.ComputesInTime.output_unique` — determinism: a machine has at most one
  completed output on a given input.
* `Turing.FinTM.computesInTime_iff`, `Turing.FinTM.Computes.exists_computesInTime_iff` —
  the space-free unfolding of a timed computation, and the completed-output
  characterization of a total machine (promoted from the epoch-1 fill).
* `Turing.FinTM.not_computesInTime_zero` — no machine computes anything in zero steps
  (the initial state is not the halting state).
* `Turing.MultiTapeTM.output_length_le`, `Turing.MultiTapeTM.output_prefix` — raw-layer
  output lemmas (at most one symbol is emitted per step, and output only grows), stated
  here rather than in the vendored `Deterministic.lean` to keep the vendored files close
  to upstream (the specification API's equations sit beside their definitions there; the
  vendored headers list them).
* `Turing.MultiTapeTM.spaceUsed_le_mul_succ` — a run of `t` steps visits at most
  `k · (t + 1)` cells (shared by the space inclusions of chapter 4; added 2026-10-10).

* `Turing.MultiTapeTM.step_output_prepend`, `Turing.MultiTapeTM.runFrom_output_prepend`,
  `Turing.MultiTapeTM.runFrom_state_ne_none_of_le` — runs commute with a fixed output
  prefix, and a live endpoint has a live past (shared run facts, 12.2c/CH7-D2;
  added 2026-10-10).
* `Turing.MultiTapeTM.exists_first_halt` — a run halted by time `t` halts first at some
  `u ≤ t`, live before `u` and already in its time-`t` configuration (the first-halt
  argument, public for the oracle query capture; added 2026-10-11, B1).
* `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — a head confined to an integer interval
  visits at most its cardinality (moved from `Build/Catalog` at MIG-0b's layering split, for
  the contract core, 2026-10-13).
* `Turing.MultiTapeTM.spaceUsed_le_of_abs_le` — if every work head stays within `r` cells of
  its start, the run uses at most `k · (2r + 1)` cells.
* `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` — after `u` steps every work head lies
  within `u` cells of its start (MIG-0b, 2026-10-13).
* `Turing.MultiTapeTM.runFrom_with_q₀`, `Turing.MultiTapeTM.initCfg_with_q₀` — a machine
  restarted at another initial state runs as before, from `Cfg.init` at that state (the core
  specification API's gate, finding 1).
* `Turing.FinTM.computesFunInTime_iff` — computing a function in time, input by input (the
  core specification API's gate, finding 2).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, §1.3.)
-/

namespace Turing

/-!
### Raw-layer output and space lemmas

Additions on top of the vendored files (kept here so the vendored `Deterministic.lean`
stays close to upstream; the specification API's equations are the exception, beside their
definitions).
-/

namespace MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- The output of an initialized run after `t` steps has length at most `t`: each step
appends at most one symbol.

**Proof sketch.** Induction on `t` with `Turing.MultiTapeTM.runFrom_succ_eq_step'` and
`Turing.MultiTapeTM.step_output` (`Option.toList` has length at most one); the initial
output is `[]`. -/
theorem output_length_le (tm : MultiTapeTM k Symbol State) (input : List Symbol) (t : ℕ) :
    ((tm.runFrom (tm.initCfg input) t).output).length ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    have hone : (tm.outputSymbol (tm.runFrom (tm.initCfg input) t)).toList.length ≤ 1 := by
      cases tm.outputSymbol (tm.runFrom (tm.initCfg input) t) <;> simp
    simp only [List.length_append]
    omega

/-- Output is monotone along a run: the output at an earlier time is a prefix of the
output at any later time.

**Proof sketch.** It suffices to treat one step (`Turing.MultiTapeTM.step_output`: a
step appends), then induct on the difference using
`Turing.MultiTapeTM.runFrom_add` and transitivity of `List.IsPrefix`. -/
theorem output_prefix (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t t' : ℕ} (h : t ≤ t') :
    (tm.runFrom cfg t).output <+: (tm.runFrom cfg t').output := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  rw [MultiTapeTM.runFrom_add]
  generalize tm.runFrom cfg t = c
  induction d with
  | zero => simp
  | succ d ih =>
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output]
    exact ih.trans (List.prefix_append _ _)

/-- A run of `t` steps visits at most `t + 1` cells on each work tape, hence at most
`k · (t + 1)` cells in all. [AB09, proof of Theorem 4.2: a machine running in time `T`
visits at most `T` cells per tape, up to the starting cell]

**Proof sketch.** Each tape's visited set is the image of `Finset.range (t + 1)`
(`Finset.card_image_le`, `Finset.card_range`); sum over the `k` tapes
(`Finset.sum_le_sum`, `Finset.sum_const_nat`). -/
theorem spaceUsed_le_mul_succ (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.spaceUsed cfg t ≤ k * (t + 1) := by
  calc tm.spaceUsed cfg t = ∑ i, tm.spaceUsedByTape cfg t i := rfl
    _ ≤ ∑ _i : Fin k, (t + 1) := Finset.sum_le_sum fun i _ => by
      unfold MultiTapeTM.spaceUsedByTape MultiTapeTM.visitedByTapeHead
      exact (Finset.card_image_le).trans (Finset.card_range (t + 1)).le
    _ = k * (t + 1) := by
      rw [Finset.sum_const_nat fun _ _ => rfl, Finset.card_univ, Fintype.card_fin]

/-- Prepending a fixed word to the output commutes with one step of any machine: the
transition table reads neither the output tape nor its length, and a step only appends
to it. This is the append-only output tape of the machine model [AB09, §1.2] (the
write-only output tape is a declared variation; see `Turing.FinTM`).

**Proof sketch.** A halted configuration does not move. Otherwise both sides apply the
same action, chosen from the unchanged state, input symbol and work-tape symbols; the
output equality is associativity of append. -/
theorem step_output_prepend (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (pre : List Symbol) :
    tm.step { cfg with output := pre ++ cfg.output } =
      { tm.step cfg with output := pre ++ (tm.step cfg).output } := by
  have hi : ({ cfg with output := pre ++ cfg.output } : Cfg k Symbol State input).inputSymbol =
      cfg.inputSymbol := rfl
  have hw : ({ cfg with output := pre ++ cfg.output } :
      Cfg k Symbol State input).workTapeSymbols = cfg.workTapeSymbols := rfl
  cases hs : cfg.state with
  | none => simp [MultiTapeTM.step, hs]
  | some q =>
    simp only [MultiTapeTM.step, hs, hi, hw]
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [Action.apply, List.append_assoc]
    rfl

/-- Prepending a fixed word to the output commutes with every run: running from a
configuration whose output already starts with `pre` yields the run's result with `pre`
still in front of its output, halted tails included [AB09, §1.2].

**Proof sketch.** Iterate the one-step commutation `step_output_prepend` along the run
with `runFrom_comm_of_step`. -/
theorem runFrom_output_prepend (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (pre : List Symbol) (t : ℕ) :
    tm.runFrom { cfg with output := pre ++ cfg.output } t =
      { tm.runFrom cfg t with output := pre ++ (tm.runFrom cfg t).output } :=
  MultiTapeTM.runFrom_comm_of_step (tm := tm) (tm' := tm)
    (fun c => { c with output := pre ++ c.output }) (fun c => step_output_prepend tm c pre) cfg t

/-- A run that is still live at time `t` was live at every time `u ≤ t`: the halting
configuration of the model is absorbing [AB09, §1.2].

**Proof sketch.** A halt at some `u ≤ t` would, by `runFrom_add` and `runFrom_of_halt`,
make the configuration at `t` equal to the halted one at `u`. -/
theorem runFrom_state_ne_none_of_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- **First halt**: if a run from `cfg` has halted by time `t`, then it halts first at
some `u ≤ t` — live at every earlier time, and already in the very configuration it
occupies at `t`, halting being absorbing [AB09, §1.2]. This is the guard-discharge form
consumed by the lockstep contracts whose hypothesis is liveness before the halting time
(`Turing.capture_run`, `Turing.emit_run`).

**Proof sketch.** Take `u` least with a halted configuration (`Nat.find`). Minimality
gives liveness below `u`; since `u ≤ t`, `runFrom_add` and `runFrom_of_halt` identify the
configurations at `u` and at `t`. -/
theorem exists_first_halt (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    {t : ℕ} (h : (tm.runFrom cfg t).state = none) :
    ∃ u ≤ t, (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  have hex : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, h⟩
  have hle : Nat.find hex ≤ t := Nat.find_min' hex h
  refine ⟨Nat.find hex, hle, fun v hv => Nat.find_min hex hv, ?_⟩
  rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_of_halt _ (Nat.find_spec hex)]

/-- **A new initial state changes no run** (the core specification API, user 2026-10-16; its
gate, finding 1): the machine `{ tm with q₀ := q }` has `tm`'s transition table, so from every
configuration it takes `tm`'s run, `({ tm with q₀ := q }).runFrom cfg t = tm.runFrom cfg t`.
A consumer restarts a machine whose initial state it does not read (for example
`Complexity.LogProg.cleanTM`) at a state of its choice, without unfolding the machine. -/
theorem runFrom_with_q₀ (tm : MultiTapeTM k Symbol State) (q : State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    ({ tm with q₀ := q } : MultiTapeTM k Symbol State).runFrom cfg t = tm.runFrom cfg t :=
  rfl

/-- **The initial configuration at a new initial state** (the core specification API; its
gate, finding 1): `({ tm with q₀ := q }).initCfg x = Cfg.init q x`. -/
theorem initCfg_with_q₀ (tm : MultiTapeTM k Symbol State) (q : State) (x : List Symbol) :
    ({ tm with q₀ := q } : MultiTapeTM k Symbol State).initCfg x = Cfg.init q x :=
  rfl

end MultiTapeTM

/-- A multi-tape Turing machine over the alphabet `Option Symbol` bundled with a finite
state type. This is the machine of [AB09, §1.2] up to the declared model variations
(append-only output tape, start-marker-free initialization — see the deviations list in
`TCSlib.Complexity.ClassP.DTIME`): the raw `MultiTapeTM` is internal plumbing, and
every headline complexity-theoretic definition is stated over `FinTM`.

The instances are data (`Fintype`/`DecidableEq`, not `Finite`) because encoding a machine
as a string requires enumerating its transition table. -/
structure FinTM (Symbol : Type) : Type 1 where
  /-- number of work tapes -/
  k : ℕ
  /-- the state type -/
  State : Type
  /-- the state type is finite, as data -/
  [fintypeState : Fintype State]
  /-- states are decidably discernible, needed to tabulate the transition function -/
  [decEqState : DecidableEq State]
  /-- the underlying machine -/
  tm : MultiTapeTM k Symbol State

namespace FinTM

attribute [instance] FinTM.fintypeState FinTM.decEqState

variable {Symbol : Type}

/-- The machine `M` halts on `input` within `t` steps with `output` written on its output
tape. Time-only variant of `Turing.MultiTapeTM.ComputesInTimeAndSpace` (the space used is
existentially discarded). [AB09, Definition 1.3] -/
def ComputesInTime (M : FinTM Symbol) (input output : List Symbol) (t : ℕ) : Prop :=
  ∃ s, M.tm.ComputesInTimeAndSpace input output t s

/-- The machine `M` computes the string function `f`, halting within `T |input|` steps on
every input. [AB09, Definition 1.3: "M computes f in T(n)-time"] -/
def ComputesFunInTime (M : FinTM Symbol) (f : List Symbol → List Symbol) (T : ℕ → ℕ) : Prop :=
  ∀ input : List Symbol, M.ComputesInTime input (f input) (T input.length)

/-- **Computing a function in time, input by input** (the core specification API, user
2026-10-16; its gate, finding 2): `M` computes `f` in time `T` exactly when, on every input
`x`, it halts within `T |x|` steps with `f x` on its output tape,
`M.ComputesFunInTime f T ↔ ∀ x, M.ComputesInTime x (f x) (T |x|)`. With
`Turing.FinTM.computesInTime_iff` this reads a function computation off the runs. -/
theorem computesFunInTime_iff (M : FinTM Symbol) (f : List Symbol → List Symbol)
    (T : ℕ → ℕ) :
    M.ComputesFunInTime f T ↔ ∀ input, M.ComputesInTime input (f input) (T input.length) :=
  Iff.rfl

/-- The machine `M`, over alphabet `Γ`, computes the string function `f` on `α`-strings
*via* the symbol embedding `e : α ↪ Γ`: on every input `x.map e` it halts within
`T |x|` steps with `(f x).map e` on its output tape. This is how a machine over a
larger alphabet is said to compute a function on a smaller one; it is the interface of
the alphabet-robustness results [AB09, §1.3.1]. -/
def ComputesFunInTimeVia {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) : Prop :=
  ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length)

/-- **Computing via an embedding, input by input** (the core specification API): `M` computes
`f` via `e` in time `T` exactly when, on every `x`, it halts on `x.map e` within `T |x|` steps
with `(f x).map e` on its output tape. -/
theorem computesFunInTimeVia_iff {α Γ : Type} (M : FinTM Γ) (e : α ↪ Γ)
    (f : List α → List α) (T : ℕ → ℕ) :
    M.ComputesFunInTimeVia e f T ↔
      ∀ x : List α, M.ComputesInTime (x.map e) ((f x).map e) (T x.length) :=
  Iff.rfl

/-- The machine `M` *computes* the string function `f`, with no time constraint: on
every input it eventually halts with `f input` on the output tape. This is the notion
of computability underlying the uncomputability results [AB09, §1.4, p. 20; §1.5];
`Turing.FinTM.ComputesFunInTime` is the time-bounded refinement, and the two are
related by `Turing.FinTM.ComputesFunInTime.computes` (below) and
`Turing.FinTM.Computes.exists_computesFunInTime`
(in `TCSlib.Complexity.Uncomputability.Computable`). -/
def Computes (M : FinTM Symbol) (f : List Symbol → List Symbol) : Prop :=
  ∀ input : List Symbol, ∃ t, M.ComputesInTime input (f input) t

/-- **Computing a function, input by input** (the core specification API): `M` computes `f`
exactly when, on every input `x`, it halts after some number of steps with `f x` on its output
tape. -/
theorem computes_iff (M : FinTM Symbol) (f : List Symbol → List Symbol) :
    M.Computes f ↔ ∀ input, ∃ t, M.ComputesInTime input (f input) t :=
  Iff.rfl

/-- Halting is absorbing, so a time bound can be weakened: if `M` produces `output`
within `t` steps it also does so within any `t' ≥ t` steps.

**Proof sketch.** By `Turing.MultiTapeTM.runFrom_add` the run to step `t'` factors through
step `t`; the state there is `none`, so `Turing.MultiTapeTM.runFrom_of_halt` shows the
configuration no longer changes, and in particular state and output at step `t'` agree with
step `t`. The space used up to step `t'` exists (it is whatever `spaceUsed` evaluates to),
which discharges the existential. -/
theorem ComputesInTime.mono {M : FinTM Symbol} {input output : List Symbol} {t t' : ℕ}
    (h : M.ComputesInTime input output t) (hle : t ≤ t') :
    M.ComputesInTime input output t' := by
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h ⊢
  obtain ⟨s, hhalt, hout, -⟩ := h
  have hrun : M.tm.runFrom (M.tm.initCfg input) t' = M.tm.runFrom (M.tm.initCfg input) t := by
    conv_lhs => rw [← Nat.add_sub_cancel' hle]
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
  exact ⟨_, by rw [hrun]; exact hhalt, by rw [hrun]; exact hout, rfl⟩

/-- No machine computes anything in zero steps: the initial configuration is in the
initial state, which is not the halting state. In particular a time budget of `0`
(e.g. from a vanishing time bound) is never satisfiable. -/
theorem not_computesInTime_zero (M : FinTM Symbol) (input output : List Symbol) :
    ¬M.ComputesInTime input output 0 := by
  rintro ⟨s, hhalt, -⟩
  simp [MultiTapeTM.runFrom_zero] at hhalt

/-- Determinism of completed outputs: a machine has at most one completed output on a
given input — if `M` halts on `input` with `w` within `t` steps and with `w'` within
`t'` steps, then `w = w'`. Together with `Turing.FinTM.ComputesInTime.mono` this
makes the halting relation of a machine a partial function.

**Proof.** Absorb both computations to time `max t t'`
(`Turing.FinTM.ComputesInTime.mono`); both then name the output of one and the same
run. -/
theorem ComputesInTime.output_unique {M : FinTM Symbol} {input w w' : List Symbol}
    {t t' : ℕ} (h : M.ComputesInTime input w t) (h' : M.ComputesInTime input w' t') :
    w = w' := by
  have h₁ := h.mono (Nat.le_max_left t t')
  have h₂ := h'.mono (Nat.le_max_right t t')
  simp only [ComputesInTime, MultiTapeTM.ComputesInTimeAndSpace] at h₁ h₂
  obtain ⟨s, -, hout, -⟩ := h₁
  obtain ⟨s', -, hout', -⟩ := h₂
  rw [← hout, ← hout']

/-- A time-bounded computation is in particular a computation. -/
theorem ComputesFunInTime.computes {M : FinTM Symbol} {f : List Symbol → List Symbol}
    {T : ℕ → ℕ} (h : M.ComputesFunInTime f T) : M.Computes f :=
  fun input => ⟨T input.length, h input⟩

/-- `ComputesInTime` without the space witness: the machine has halted by time `t`
with completed output exactly `w`. The space existential is uniquely determined by
the run, so it can always be discharged. (Promoted from the epoch-1 fill and
generalized from `Bool` to an arbitrary alphabet, per the epoch-1 audit,
finding 4.) -/
theorem computesInTime_iff (M : FinTM Symbol) (x w : List Symbol) (t : ℕ) :
    M.ComputesInTime x w t ↔
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = w := by
  constructor
  · rintro ⟨s, hs, ho, -⟩
    exact ⟨hs, ho⟩
  · rintro ⟨hs, ho⟩
    exact ⟨_, hs, ho, rfl⟩

/-- A total machine's completed outputs are exactly its prescribed values: if `M`
computes `g`, then `M` halts on `x` with completed output `w` — in some number of
steps — iff `w = g x`. Existence of a computation together with determinism of
completed outputs (`Turing.FinTM.ComputesInTime.output_unique`). (Promoted from
the epoch-1 fill per the epoch-1 audit, finding 4.) -/
theorem Computes.exists_computesInTime_iff {M : FinTM Symbol}
    {g : List Symbol → List Symbol} (hM : M.Computes g) (x w : List Symbol) :
    (∃ t, M.ComputesInTime x w t) ↔ w = g x := by
  obtain ⟨t, ht⟩ := hM x
  constructor
  · rintro ⟨s, hs⟩
    exact hs.output_unique ht
  · rintro rfl
    exact ⟨t, ht⟩

end FinTM

end Turing

namespace Turing

/-- A head confined to an integer interval visits at most its cardinality.

(Moved from `Build/Zone.lean` for B4, 2026-10-12.)

**Proof sketch.** The visited set is a finite image contained in the
interval by hypothesis; `Finset.card_le_card` and `Int.card_Icc` finish. -/
theorem MultiTapeTM.spaceUsedByTape_le_card_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t : ℕ) (i : Fin k) (lo hi : ℤ)
    (h : ∀ u ≤ t, (tm.runFrom d u).workTapePos i ∈ Finset.Icc lo hi) :
    tm.spaceUsedByTape d t i ≤ (hi + 1 - lo).toNat := by
  unfold MultiTapeTM.spaceUsedByTape
  calc
    _ ≤ (Finset.Icc lo hi).card := Finset.card_le_card (by
      intro p hp
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hp
      exact h u (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hu))
    _ = _ := Int.card_Icc lo hi

/-- **A common head radius bounds the space**: if up to time `t` every work head stays within `r`
cells of its starting position, the run visits at most `2r + 1` cells on each work tape, hence
at most `k · (2r + 1)` cells in all.

**Proof sketch.** Each head stays in the integer interval of radius `r` around its start, which
has `2r + 1` cells (`Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`); sum over the tapes
(`Turing.MultiTapeTM.spaceUsed_eq_sum`). -/
theorem MultiTapeTM.spaceUsed_le_of_abs_le {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State)
    (d : Cfg k Symbol State input) (t r : ℕ)
    (h : ∀ u ≤ t, ∀ j, |(tm.runFrom d u).workTapePos j - d.workTapePos j| ≤ (r : ℤ)) :
    tm.spaceUsed d t ≤ k * (2 * r + 1) := by
  rw [MultiTapeTM.spaceUsed_eq_sum]
  calc
    ∑ j, tm.spaceUsedByTape d t j ≤ ∑ _j : Fin k, (2 * r + 1) := by
      refine Finset.sum_le_sum fun j _ => ?_
      have hb := tm.spaceUsedByTape_le_card_Icc d t j (d.workTapePos j - r)
        (d.workTapePos j + r) fun u hu => by
          have he := abs_le.mp (h u hu j)
          rw [Finset.mem_Icc]
          constructor <;> omega
      omega
    _ = k * (2 * r + 1) := by simp

end Turing

namespace Turing

/-- **The time-derived head envelope** (MIG-0b): after `u` steps from `cfg`, every work head
lies within `u` cells of its start. Every row with a time bound therefore has an interval
envelope, even when it states none (the install and emit calls; the find round). It is the
interval form of `Build/Catalog`'s private `f2_head_steps`, which retires with MIG-1 (backlog
F6-1(g)), and of the run head bound that the H2 promotion exports
(`CodeSimulator.h1Run_headBound`, backlog F7-1(a)); stated here over any alphabet and state
type, like the raw layer it extends.

**Proof sketch.** Induction on `u`: each step moves a head by at most one cell
(`Turing.MultiTapeTM.workTapePos_step_le`). -/
theorem MultiTapeTM.workTapePos_runFrom_mem_Icc {k : ℕ} {Symbol State : Type*}
    {input : List Symbol} (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input)
    (u : ℕ) (j : Fin k) :
    (tm.runFrom cfg u).workTapePos j ∈
      Finset.Icc (cfg.workTapePos j - u) (cfg.workTapePos j + u) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hs := abs_le.mp (tm.workTapePos_step_le (tm.runFrom cfg u) j)
    rw [Finset.mem_Icc] at ih ⊢
    rw [MultiTapeTM.runFrom_succ_eq_step']
    push_cast
    constructor <;> omega

end Turing
```

## ===== TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.ChoiceReplay
import TCSlib.Complexity.TuringMachine.Build.StepClock
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.CfgFacts

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The exhaustive replay of a fixed NDTM

[AB09, §3.2, proof of Theorem 3.2]: the complement of a nondeterministic language is decidable
deterministically in exponential time "by examining all the possibilities for the machine's
nondeterministic choices", and that simulation suffices for the nondeterministic time
hierarchy. `Turing.FinNDTM.exists_exhaustiveDecider` is that simulation
for a fixed NDTM, as a public generic theorem (user decision 2 of 2026-10-13): on every input on
which all branches halt within `T`, a deterministic machine decides acceptance within
`C·2^{C·(T + 1)}`, with no input-length term. The exponential decider of the hierarchy is then
`BF := E(UN)`, the exhaustive replay of the universal NDTM; its statement is derived here
(`Turing.ndAcceptsWithin_decider_of_universal`, proved).

## Main definitions

No new definitions: the exhaustive replay and `BF` are existential contracts.

## Main results

* `Turing.FinNDTM.exists_exhaustiveDecider` — the exhaustive replay `E` (proved).
* `Turing.ndAcceptsWithin_decider_of_universal` — `BF := E(UN)` (proved).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2, proof of Theorem 3.2.)
-/

namespace Turing

/-! ### The construction of the exhaustive replay (the `xr_` privates)

The semantic and arithmetic parts of the exhaustive replay, read through the published ND
semantics only: no branch halts at depth `0`; a branch of length `|w|` stays within the
radius-`|w|` window; at an all-halting depth `L ≤ T` acceptance within `L` and within `T`
agree; the first all-halting depth exists; the ledger's shape. Then two generic tools for the
machine: the translation of work tapes (a branch started on blank tapes at displaced heads is
the branch from `initCfg`, translated), and the first arrival at a stationary anchor (the
phase host's guard for every leaf row of this file). -/

/-- No branch of length `0` has halted: `Cfg.init` is live. -/
private theorem xr_not_haltsWithin_zero (N : FinNDTM Bool) (z : List Bool) :
    ¬ N.tm.HaltsWithin z 0 := by
  intro h
  have h0 := NDTM.haltsWithin_iff.mp h [] rfl
  rw [NDTM.runWith_nil, NDTM.initCfg_eq, Cfg.init_state] at h0
  exact Option.some_ne_none _ h0

/-- One step from the radius-`s` window stays in the radius-`s + 1` window, with the output
growing by at most one symbol. -/
private theorem xr_window_stepWith {k : ℕ} {S : Type} {x : List Bool} (tm : NDTM k Bool S)
    (b : Bool) (c : Cfg k Bool S x) (s : ℕ)
    (hpos : ∀ i, |c.workTapePos i| ≤ (s : ℤ))
    (hblank : ∀ i (p : ℤ), (s : ℤ) < |p| → c.workTapes i p = none)
    (hout : c.output.length ≤ s) :
    (∀ i, |(tm.stepWith b c).workTapePos i| ≤ ((s + 1 : ℕ) : ℤ)) ∧
    (∀ i (p : ℤ), ((s + 1 : ℕ) : ℤ) < |p| → (tm.stepWith b c).workTapes i p = none) ∧
    (tm.stepWith b c).output.length ≤ s + 1 := by
  cases hq : c.state with
  | none =>
    rw [NDTM.stepWith_of_halt hq]
    refine ⟨fun i => (hpos i).trans (by push_cast; omega), fun i p hp => hblank i p ?_, by omega⟩
    push_cast at hp; linarith
  | some q =>
    rw [NDTM.stepWith_of_some hq]
    refine ⟨fun i => ?_, fun i p hp => ?_, ?_⟩
    · have h1 := workTapePos_apply_le (tm.tr b q c.inputSymbol c.workTapeSymbols) c i
      have h2 := hpos i
      rw [abs_le] at h1 h2 ⊢
      push_cast
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    · rw [Action.apply_workTapes]
      have h2 := hpos i
      have hp' : (s : ℤ) < |p| := by push_cast at hp; linarith
      have hne : p ≠ c.workTapePos i := by
        rintro rfl
        exact absurd h2 (not_le.mpr hp')
      rw [Function.update_of_ne hne]
      exact hblank i p hp'
    · rw [Action.apply_output, List.length_append]
      have : (tm.tr b q c.inputSymbol c.workTapeSymbols).output.toList.length ≤ 1 := by
        cases (tm.tr b q c.inputSymbol c.workTapeSymbols).output <;> simp
      omega

/-- After a branch of length `|w|` from the initial configuration, every work head lies within
`|w|` of its origin, every cell beyond radius `|w|` is blank, and the output has length at most
`|w|`: the window the clear must blank. -/
private theorem xr_window_runWith {k : ℕ} {S : Type} (tm : NDTM k Bool S) (z w : List Bool) :
    (∀ i, |(tm.runWith w (tm.initCfg z)).workTapePos i| ≤ (w.length : ℤ)) ∧
    (∀ i (p : ℤ), (w.length : ℤ) < |p| → (tm.runWith w (tm.initCfg z)).workTapes i p = none) ∧
    (tm.runWith w (tm.initCfg z)).output.length ≤ w.length := by
  suffices H : ∀ (w : List Bool) (c : Cfg k Bool S z) (s : ℕ),
      (∀ i, |c.workTapePos i| ≤ (s : ℤ)) →
      (∀ i (p : ℤ), (s : ℤ) < |p| → c.workTapes i p = none) →
      c.output.length ≤ s →
      (∀ i, |(tm.runWith w c).workTapePos i| ≤ ((s + w.length : ℕ) : ℤ)) ∧
      (∀ i (p : ℤ), ((s + w.length : ℕ) : ℤ) < |p| → (tm.runWith w c).workTapes i p = none) ∧
      (tm.runWith w c).output.length ≤ s + w.length by
    have h := H w (tm.initCfg z) 0
      (fun i => by rw [NDTM.initCfg_eq, Cfg.init_workTapePos]; simp)
      (fun i p _ => by rw [NDTM.initCfg_eq, Cfg.init_workTapes])
      (by rw [NDTM.initCfg_eq, Cfg.init_output]; simp)
    simpa only [Nat.zero_add] using h
  intro w
  induction w with
  | nil =>
    intro c s h1 h2 h3
    simp only [NDTM.runWith_nil, List.length_nil, Nat.add_zero]
    exact ⟨h1, h2, h3⟩
  | cons b w ih =>
    intro c s h1 h2 h3
    obtain ⟨g1, g2, g3⟩ := xr_window_stepWith tm b c s h1 h2 h3
    have := ih (tm.stepWith b c) (s + 1) g1 g2 g3
    rw [NDTM.runWith_cons]
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using this

/-- At an all-halting depth `L ≤ T`, acceptance within `L` and within `T` agree: one direction
is monotonicity, the other truncates an accepting word of length `T` at `L`. -/
private theorem xr_accepts_iff_of_halts (N : FinNDTM Bool) (z : List Bool) {L T : ℕ}
    (hL : N.tm.HaltsWithin z L) (hLT : L ≤ T) :
    N.AcceptsWithin z L ↔ N.AcceptsWithin z T := by
  refine ⟨fun h => h.mono hLT, fun h => ?_⟩
  obtain ⟨w, hw, hhalt, hout⟩ := FinNDTM.acceptsWithin_iff.mp h
  have htake : (w.take L).length = L := by rw [List.length_take, hw]; omega
  have hstop := NDTM.haltsWithin_iff.mp hL (w.take L) htake
  have hsplit : N.tm.runWith w (N.tm.initCfg z) = N.tm.runWith (w.take L) (N.tm.initCfg z) := by
    conv_lhs => rw [← List.take_append_drop L w]
    rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hstop]
  rw [hsplit] at hout
  exact FinNDTM.acceptsWithin_iff.mpr ⟨w.take L, htake, hstop, hout⟩

/-- The first all-halting depth exists below any all-halting bound, is positive, and answers
as the bound does: the deepening terminates by depth `T`, never at depth `0`. -/
private theorem xr_first_depth (N : FinNDTM Bool) (z : List Bool) (T : ℕ)
    (hT : N.tm.HaltsWithin z T) :
    ∃ L, 0 < L ∧ L ≤ T ∧ N.tm.HaltsWithin z L ∧ (∀ L' < L, ¬ N.tm.HaltsWithin z L') ∧
      (N.AcceptsWithin z L ↔ N.AcceptsWithin z T) := by
  classical
  have hex : ∃ L, N.tm.HaltsWithin z L := ⟨T, hT⟩
  refine ⟨Nat.find hex, ?_, Nat.find_min' hex hT, Nat.find_spec hex,
    fun L' hL' => Nat.find_min hex hL', xr_accepts_iff_of_halts N z (Nat.find_spec hex)
      (Nat.find_min' hex hT)⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
  · exact absurd (h0 ▸ Nat.find_spec hex) (xr_not_haltsWithin_zero N z)
  · exact h0

/-- The ledger's shape, with two steps of slack for the dispatch and the answer:
`Σ_{L ≤ T} 2^L · A(L + 1) + 2 ≤ (A + 3)·2^{(A + 3)(T + 1)}`. -/
private theorem xr_ledger (A T : ℕ) :
    ∑ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) + 2 ≤
      (A + 3) * 2 ^ ((A + 3) * (T + 1)) := by
  have hterm : ∀ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) ≤ 2 ^ T * (A * (T + 1)) := by
    intro L hL
    rw [Finset.mem_range] at hL
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) (by omega))
      (Nat.mul_le_mul_left A (by omega))
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range] at hsum
  change _ ≤ (T + 1) * (2 ^ T * (A * (T + 1))) at hsum
  have hlin : T + 1 ≤ 2 ^ (T + 1) := (Nat.lt_two_pow_self).le
  have h2 : 2 ^ T ≤ 2 ^ (T + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow : 2 ^ (T + 1) * 2 ^ (T + 1) * 2 ^ (T + 1) ≤ 2 ^ ((A + 3) * (T + 1)) := by
    rw [← pow_add, ← pow_add]
    exact Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hone : 1 ≤ 2 ^ ((A + 3) * (T + 1)) := Nat.one_le_two_pow
  calc ∑ L ∈ Finset.range (T + 1), 2 ^ L * (A * (L + 1)) + 2
      ≤ (T + 1) * (2 ^ T * (A * (T + 1))) + 2 := Nat.add_le_add_right hsum 2
    _ = A * ((T + 1) * 2 ^ T * (T + 1)) + 2 := by ring
    _ ≤ A * (2 ^ (T + 1) * 2 ^ (T + 1) * 2 ^ (T + 1)) + 2 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left A (Nat.mul_le_mul (Nat.mul_le_mul hlin h2) hlin)) 2
    _ ≤ A * 2 ^ ((A + 3) * (T + 1)) + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left A hpow) 2
    _ ≤ (A + 3) * 2 ^ ((A + 3) * (T + 1)) := by nlinarith [hone]

/-! #### Translation of work tapes -/

/-- The configuration `c` with work tape `i` translated by `δ i`: cell `p` holds what cell
`p - δ i` held, and the head moves by `δ i`; the state, input head and output are `c`'s. -/
private def xr_shift {k : ℕ} {S : Type} {x : List Bool} (δ : Fin k → ℤ) (c : Cfg k Bool S x) :
    Cfg k Bool S x :=
  ⟨c.state, c.inputPos, fun i p => c.workTapes i (p - δ i), fun i => c.workTapePos i + δ i,
    c.output⟩

/-- A translated configuration reads the same work symbols. -/
private theorem xr_workTapeSymbols_shift {k : ℕ} {S : Type} {x : List Bool} (δ : Fin k → ℤ)
    (c : Cfg k Bool S x) : (xr_shift δ c).workTapeSymbols = c.workTapeSymbols := by
  funext i
  rw [Cfg.workTapeSymbols_eq, Cfg.workTapeSymbols_eq]
  show c.workTapes i (c.workTapePos i + δ i - δ i) = _
  rw [add_sub_cancel_right]

/-- Applying an action commutes with translation. -/
private theorem xr_apply_shift {k : ℕ} {S : Type} {x : List Bool} (δ : Fin k → ℤ)
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    a.apply (xr_shift δ c) = xr_shift δ (a.apply c) := by
  apply Cfg.ext
  · show (a.apply (xr_shift δ c)).state = (a.apply c).state
    rw [Action.apply_state, Action.apply_state]
  · show (a.apply (xr_shift δ c)).inputPos = (a.apply c).inputPos
    rw [Action.apply_inputPos, Action.apply_inputPos]
    rfl
  · funext i p
    show (a.apply (xr_shift δ c)).workTapes i p = (a.apply c).workTapes i (p - δ i)
    rw [Action.apply_workTapes, Action.apply_workTapes, xr_workTapeSymbols_shift]
    show Function.update (fun p => c.workTapes i (p - δ i)) (c.workTapePos i + δ i) _ p = _
    by_cases hp : p = c.workTapePos i + δ i
    · subst hp
      rw [Function.update_self, add_sub_cancel_right, Function.update_self]
    · rw [Function.update_of_ne hp, Function.update_of_ne (by omega)]
  · funext i
    show (a.apply (xr_shift δ c)).workTapePos i = (a.apply c).workTapePos i + δ i
    rw [Action.apply_workTapePos, Action.apply_workTapePos]
    show c.workTapePos i + δ i + _ = c.workTapePos i + _ + δ i
    ring
  · show (a.apply (xr_shift δ c)).output = (a.apply c).output
    rw [Action.apply_output, Action.apply_output]
    rfl

/-- One nondeterministic step commutes with translation. -/
private theorem xr_stepWith_shift {k : ℕ} {S : Type} {x : List Bool} (N : NDTM k Bool S)
    (δ : Fin k → ℤ) (b : Bool) (c : Cfg k Bool S x) :
    N.stepWith b (xr_shift δ c) = xr_shift δ (N.stepWith b c) := by
  cases hq : c.state with
  | none =>
    rw [NDTM.stepWith_of_halt hq, NDTM.stepWith_of_halt (show (xr_shift δ c).state = none from hq)]
  | some q =>
    rw [NDTM.stepWith_of_some hq,
      NDTM.stepWith_of_some (show (xr_shift δ c).state = some q from hq),
      Cfg.inputSymbol_congr (xr_shift δ c) c rfl, xr_workTapeSymbols_shift, xr_apply_shift]

/-- A branch commutes with translation: the branch along `w` from a translated configuration
is the translated branch. -/
private theorem xr_runWith_shift {k : ℕ} {S : Type} {x : List Bool} (N : NDTM k Bool S)
    (δ : Fin k → ℤ) (w : List Bool) (c : Cfg k Bool S x) :
    N.runWith w (xr_shift δ c) = xr_shift δ (N.runWith w c) := by
  induction w generalizing c with
  | nil => rw [NDTM.runWith_nil, NDTM.runWith_nil]
  | cons b w ih => rw [NDTM.runWith_cons, NDTM.runWith_cons, xr_stepWith_shift, ih]

/-! #### The first arrival at a stationary anchor -/

/-- A configuration fixed by one step is fixed by every run. -/
private theorem xr_runFrom_fixed {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (d : Cfg k Bool S x) (hd : tm.step d = d) (n : ℕ) : tm.runFrom d n = d := by
  induction n with
  | zero => exact MultiTapeTM.runFrom_zero
  | succ n ih => rw [MultiTapeTM.runFrom_succ_eq_step', ih, hd]

open MultiTapeTM in
/-- One step of a run. -/
private theorem xr_runFrom_one {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (d : Cfg k Bool S x) : tm.runFrom d 1 = tm.step d := by
  rw [runFrom_succ_eq_step', runFrom_zero]

/-- Two steps of a run. -/
private theorem xr_runFrom_two {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (d : Cfg k Bool S x) : tm.runFrom d 2 = tm.step (tm.step d) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, MultiTapeTM.runFrom_add, xr_runFrom_one, xr_runFrom_one]

/-- **The first arrival at a stationary anchor.** If a run reaches `c'` in state `a` at time `T`
and `a` is stationary, the first time the state is `a` is at most `T`, reaches `c'` too, and no
earlier state is `a`: the phase host's guard, for free, from an exact-time run lemma. -/
private theorem xr_firstArrival {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (a : S) (hstat : ∀ d : Cfg k Bool S x, d.state = some a → tm.step d = d)
    {c c' : Cfg k Bool S x} {T : ℕ} (h : tm.runFrom c T = c') (hc' : c'.state = some a) :
    ∃ T' ≤ T, tm.runFrom c T' = c' ∧ ∀ u < T', (tm.runFrom c u).state ≠ some a := by
  classical
  have hT' : (tm.runFrom c T).state = some a := by rw [h]; exact hc'
  have hex : ∃ u, (tm.runFrom c u).state = some a := ⟨T, hT'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_, fun u hu => Nat.find_min hex hu⟩
  have hsplit : tm.runFrom c T = tm.runFrom (tm.runFrom c (Nat.find hex)) (T - Nat.find hex) := by
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' (Nat.find_min' hex hT')]
  rw [xr_runFrom_fixed tm _ (hstat _ (Nat.find_spec hex))] at hsplit
  exact hsplit.symm.trans h
/-! #### The leaf rows

This file's own rows, on `Bool` tapes, each exiting at a stationary anchor `done b`: the
ruler-driven pass (the window clear's engine), the head rewind to a word's origin, the extension
of a word by one `false`, the capture test (which also clears the captured output), the input
rewind and the answer. Their run lemmas give exact times and exact configurations; the phase
host's guard comes from `xr_firstArrival`. -/

/-- The control of the leaf rows. -/
private inductive xr_St where
  | start
  | run
  | aux
  | back (b : Bool)
  | done (b : Bool)
  deriving DecidableEq, Fintype

/-- A silent action: no input move and no emission. -/
private def xr_act {K : ℕ} (mv : Fin K → Option (Option Bool) × SignType) (q : Option xr_St) :
    Action K Bool xr_St := ⟨0, mv, none, q⟩

/-- Write `wr` and move `m` on tape `r` only. -/
private def xr_mv1 {K : ℕ} (r : Fin K) (wr : Option (Option Bool)) (m : SignType) :
    Fin K → Option (Option Bool) × SignType :=
  fun i => if i = r then (wr, m) else (none, 0)

/-- Write `wr` and move `m` on tape `j`, move `m'` on tape `r`. -/
private def xr_mv2 {K : ℕ} (j r : Fin K) (wr : Option (Option Bool)) (m m' : SignType) :
    Fin K → Option (Option Bool) × SignType :=
  fun i => if i = j then (wr, m) else if i = r then (none, m') else (none, 0)

/-- The stationary action at `q`. -/
private def xr_stay {K : ℕ} (q : xr_St) : Action K Bool xr_St :=
  xr_act (fun _ => (none, 0)) (some q)

private theorem xr_cast_pos : ((SignType.pos : SignType) : ℤ) = 1 := rfl
private theorem xr_cast_neg : ((SignType.neg : SignType) : ℤ) = -1 := rfl

/-- A silent action's effect: the state, the writes under the heads, the head moves. -/
private theorem xr_act_apply {K : ℕ} {x : List Bool}
    (mv : Fin K → Option (Option Bool) × SignType) (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act mv q).apply d =
      ⟨q, d.inputPos,
        fun i => Function.update (d.workTapes i) (d.workTapePos i)
          ((mv i).1.getD (d.workTapes i (d.workTapePos i))),
        fun i => d.workTapePos i + ((mv i).2 : ℤ), d.output⟩ := by
  apply Cfg.ext
  · exact Action.apply_state _ _
  · exact (Action.apply_inputPos _ _).trans (moveInputPos_zero _)
  · funext i
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    rfl
  · funext i
    exact Action.apply_workTapePos _ _ _
  · exact (Action.apply_output _ _).trans (List.append_nil _)

/-- A one-tape write-and-move. -/
private theorem xr_mv1_apply {K : ℕ} {x : List Bool} (r : Fin K) (wr : Option (Option Bool))
    (m : SignType) (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act (xr_mv1 r wr m) q).apply d =
      ⟨q, d.inputPos,
        Function.update d.workTapes r (Function.update (d.workTapes r) (d.workTapePos r)
          (wr.getD (d.workTapes r (d.workTapePos r)))),
        Function.update d.workTapePos r (d.workTapePos r + (m : ℤ)), d.output⟩ := by
  rw [xr_act_apply]
  congr 1
  · funext i
    by_cases hi : i = r
    · rw [hi]
      simp [xr_mv1]
    · simp [xr_mv1, hi]
  · funext i
    by_cases hi : i = r
    · rw [hi]
      simp [xr_mv1]
    · simp [xr_mv1, hi]

/-- A one-tape move without a write. -/
private theorem xr_mv1_apply_none {K : ℕ} {x : List Bool} (r : Fin K) (m : SignType)
    (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act (xr_mv1 r none m) q).apply d =
      ⟨q, d.inputPos, d.workTapes,
        Function.update d.workTapePos r (d.workTapePos r + (m : ℤ)), d.output⟩ := by
  rw [xr_mv1_apply]
  congr 1
  simp

/-- A two-tape move: a write-and-move on `j`, a move on `r`. -/
private theorem xr_mv2_apply {K : ℕ} {x : List Bool} (j r : Fin K) (hjr : j ≠ r)
    (wr : Option (Option Bool)) (m m' : SignType) (q : Option xr_St) (d : Cfg K Bool xr_St x) :
    (xr_act (xr_mv2 j r wr m m') q).apply d =
      ⟨q, d.inputPos,
        Function.update d.workTapes j (Function.update (d.workTapes j) (d.workTapePos j)
          (wr.getD (d.workTapes j (d.workTapePos j)))),
        fun i => if i = j then d.workTapePos j + (m : ℤ)
          else if i = r then d.workTapePos r + (m' : ℤ) else d.workTapePos i, d.output⟩ := by
  rw [xr_act_apply]
  congr 1
  · funext i
    by_cases hij : i = j
    · rw [hij]
      simp [xr_mv2]
    · by_cases hir : i = r
      · rw [hir]
        simp [xr_mv2, Ne.symm hjr]
      · simp [xr_mv2, hij, hir]
  · funext i
    by_cases hij : i = j
    · rw [hij]
      simp [xr_mv2]
    · by_cases hir : i = r
      · rw [hir]
        simp [xr_mv2, Ne.symm hjr]
      · simp [xr_mv2, hij, hir]

/-- A state whose table is the stationary action fixes every configuration in that state. -/
private theorem xr_stay_step {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St) (q : xr_St)
    (htr : ∀ inp w, tm.tr q inp w = xr_stay q) (d : Cfg K Bool xr_St x) (hd : d.state = some q) :
    tm.step d = d := by
  rw [MultiTapeTM.step_of_some hd, htr, xr_stay, xr_act_apply]
  apply Cfg.ext
  · exact hd.symm
  · rfl
  · funext i
    simp
  · funext i
    simp
  · rfl

/-- **The return pass** of the leaf rows. From `back b` with the head on the rightmost of the `m`
non-blank cells `o, …, o + m - 1` and a blank at `o - 1`, `m + 1` steps write `wb` on those `m`
cells, return the head to `o`, and stop at `done b`. -/
private theorem xr_back_run {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St) (r : Fin K)
    (wb : Option (Option Bool))
    (hsome : ∀ (b : Bool) inp w s, w r = some s →
      tm.tr (.back b) inp w = xr_act (xr_mv1 r wb SignType.neg) (some (.back b)))
    (hnone : ∀ (b : Bool) inp w, w r = none →
      tm.tr (.back b) inp w = xr_act (xr_mv1 r none SignType.pos) (some (.done b)))
    (b : Bool) (o : ℤ) (m : ℕ) :
    ∀ d : Cfg K Bool xr_St x, d.state = some (.back b) → d.workTapePos r = o + m - 1 →
      (∀ i : ℕ, i < m → d.workTapes r (o + i) ≠ none) → d.workTapes r (o - 1) = none →
      tm.runFrom d (m + 1) =
        ⟨some (.done b), d.inputPos,
          Function.update d.workTapes r
            (fun p => if o ≤ p ∧ p < o + m then wb.getD (d.workTapes r p) else d.workTapes r p),
          Function.update d.workTapePos r o, d.output⟩ := by
  induction m with
  | zero =>
    intro d hd hpos _ hleft
    have hread : d.workTapeSymbols r = none := by
      rw [Cfg.workTapeSymbols_eq, hpos]
      simpa using hleft
    rw [show (0 : ℕ) + 1 = 1 from rfl, xr_runFrom_one, MultiTapeTM.step_of_some hd,
      hnone b _ _ hread, xr_mv1_apply_none]
    congr 1
    · symm
      rw [Function.update_eq_self_iff]
      funext p
      split_ifs with h
      · exfalso
        push_cast at h
        omega
      · rfl
    · rw [hpos, xr_cast_pos]
      congr 1
      push_cast
      ring
  | succ m ih =>
    intro d hd hpos hcells hleft
    have hcur : d.workTapes r (o + m) ≠ none := hcells m (by omega)
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hcur
    have hpos' : d.workTapePos r = o + m := by rw [hpos]; push_cast; ring
    have hread : d.workTapeSymbols r = some s := by
      rw [Cfg.workTapeSymbols_eq, hpos', hs]
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step_of_some hd, hsome b _ _ s hread,
      xr_mv1_apply, hpos', xr_cast_neg]
    have hX : ∀ p : ℤ, p ≠ o + m →
        Function.update (d.workTapes r) (o + m) (wb.getD (d.workTapes r (o + m))) p =
          d.workTapes r p := fun p hp => Function.update_of_ne hp _ _
    rw [ih _ rfl ?_ ?_ ?_]
    · dsimp only
      simp only [Function.update_self, Function.update_idem]
      congr 1
      refine congrArg (Function.update d.workTapes r) (funext fun p => ?_)
      dsimp only
      by_cases hp : p = o + m
      · rw [hp, Function.update_self, if_neg (fun h => lt_irrefl _ h.2),
          if_pos ⟨by omega, by push_cast; omega⟩]
      · rw [hX p hp]
        by_cases h1 : o ≤ p ∧ p < o + m
        · rw [if_pos h1, if_pos ⟨h1.1, by push_cast; omega⟩]
        · rw [if_neg h1, if_neg (by push_cast at h1 ⊢; omega)]
    · dsimp only
      rw [Function.update_self]
      omega
    · intro i hi
      dsimp only
      rw [Function.update_self, hX _ (by omega)]
      exact hcells i (by omega)
    · dsimp only
      rw [Function.update_self, hX _ (by omega)]
      exact hleft

/-- **The forward scan** of the leaf rows: from `run` with the head at `o` and `m` non-blank
cells ahead, `m` steps move the head to `o + m` and change nothing else. -/
private theorem xr_fwd_run {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St) (r : Fin K)
    (hsome : ∀ inp w s, w r = some s →
      tm.tr .run inp w = xr_act (xr_mv1 r none SignType.pos) (some .run))
    (m : ℕ) :
    ∀ (o : ℤ) (d : Cfg K Bool xr_St x), d.state = some .run → d.workTapePos r = o →
      (∀ i : ℕ, i < m → d.workTapes r (o + i) ≠ none) →
      tm.runFrom d m =
        ⟨some .run, d.inputPos, d.workTapes, Function.update d.workTapePos r (o + m),
          d.output⟩ := by
  induction m with
  | zero =>
    intro o d hd hpos _
    rw [MultiTapeTM.runFrom_zero]
    apply Cfg.ext
    · exact hd
    · rfl
    · rfl
    · funext i
      dsimp only
      by_cases hi : i = r
      · rw [hi, Function.update_self, hpos]
        simp
      · rw [Function.update_of_ne hi]
    · rfl
  | succ m ih =>
    intro o d hd hpos hcells
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hcells 0 (by omega))
    have hread : d.workTapeSymbols r = some s := by
      rw [Cfg.workTapeSymbols_eq, hpos]
      simpa using hs
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step_of_some hd, hsome _ _ s hread,
      xr_mv1_apply_none, hpos, xr_cast_pos]
    rw [ih (o + 1) _ rfl (by dsimp only; rw [Function.update_self]) ?_]
    · dsimp only
      rw [Function.update_idem]
      congr 2
      push_cast
      ring
    · intro i hi
      dsimp only
      have := hcells (i + 1) (by omega)
      push_cast at this ⊢
      convert this using 2
      ring

/-- **The rewind**: one step left, then left while reading a symbol, then one step right at the
blank. -/
private def xr_rewindTM (K : ℕ) (r : Fin K) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q _ w =>
    match q with
    | .start => xr_act (xr_mv1 r none SignType.neg) (some (.back true))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- From any head position `p₀ ≤ |u|` on the word `u` at the origin, the rewind returns the head
to `0` in `p₀ + 2` steps, changes nothing else, and stops at `done true`. -/
private theorem xr_rewindTM_run {K : ℕ} {x : List Bool} (r : Fin K) (u : List Bool) (p₀ : ℕ)
    (hp₀ : p₀ ≤ u.length) (d : Cfg K Bool xr_St x) (hd : d.state = some .start)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = p₀) :
    (xr_rewindTM K r).runFrom d (p₀ + 2) =
      ⟨some (.done true), d.inputPos, d.workTapes, Function.update d.workTapePos r 0,
        d.output⟩ := by
  rw [show p₀ + 2 = (p₀ + 1) + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step,
    MultiTapeTM.step_of_some hd,
    show (xr_rewindTM K r).tr .start _ _ =
      xr_act (xr_mv1 r none SignType.neg) (some (.back true)) from rfl,
    xr_mv1_apply_none, hpos, xr_cast_neg]
  rw [xr_back_run (xr_rewindTM K r) r none
    (fun b inp w s hs => by simp [xr_rewindTM, hs]) (fun b inp w hw => by simp [xr_rewindTM, hw])
    true 0 p₀ _ rfl ?_ ?_ ?_]
  · dsimp only
    rw [Function.update_idem]
    congr 1
    rw [Function.update_eq_self_iff]
    funext p
    simp
  · dsimp only
    rw [Function.update_self]
    ring
  · intro i hi
    dsimp only
    rw [zero_add, hr, FinTM.bufferTape_nat, ne_eq, List.getElem?_eq_none_iff]
    omega
  · dsimp only
    rw [hr]
    simp

/-- **The extension**: right while reading a symbol, write `false` at the blank and turn, return
to the origin: the word grows by one `false`. -/
private def xr_extendTM (K : ℕ) (r : Fin K) : MultiTapeTM K Bool xr_St where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.pos) (some .run)
      | none => xr_act (xr_mv1 r (some (some false)) SignType.neg) (some (.back true))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- From the origin of the word `u`, the extension writes `u ++ [false]` in `2|u| + 2` steps,
returns the head to `0`, changes nothing else, and stops at `done true`. -/
private theorem xr_extendTM_run {K : ℕ} {x : List Bool} (r : Fin K) (u : List Bool)
    (d : Cfg K Bool xr_St x) (hd : d.state = some .run)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = 0) :
    (xr_extendTM K r).runFrom d (2 * u.length + 2) =
      ⟨some (.done true), d.inputPos,
        Function.update d.workTapes r (FinTM.bufferTape (u ++ [false])),
        Function.update d.workTapePos r 0, d.output⟩ := by
  have hcells : ∀ i : ℕ, i < u.length → d.workTapes r ((0 : ℤ) + i) ≠ none := by
    intro i hi
    rw [zero_add, hr, FinTM.bufferTape_nat, ne_eq, List.getElem?_eq_none_iff]
    omega
  have h1 : (xr_extendTM K r).runFrom d u.length = ⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r (u.length : ℤ), d.output⟩ := by
    rw [xr_fwd_run (xr_extendTM K r) r (fun inp w s hs => by simp [xr_extendTM, hs])
      u.length 0 d hd hpos hcells, zero_add]
  have hend : (⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r (u.length : ℤ), d.output⟩ :
      Cfg K Bool xr_St x).workTapeSymbols r = none := by
    rw [Cfg.workTapeSymbols_eq]
    dsimp only
    rw [Function.update_self, hr, FinTM.bufferTape_nat]
    simp
  have h2 : (xr_extendTM K r).step ⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r (u.length : ℤ), d.output⟩ =
      ⟨some (.back true), d.inputPos,
        Function.update d.workTapes r (FinTM.bufferTape (u ++ [false])),
        Function.update d.workTapePos r ((u.length : ℤ) + -1), d.output⟩ := by
    rw [MultiTapeTM.step_of_some rfl,
      show (xr_extendTM K r).tr .run _ _ =
        xr_act (xr_mv1 r (some (some false)) SignType.neg) (some (.back true)) by
          simp only [xr_extendTM]
          rw [hend],
      xr_mv1_apply, xr_cast_neg]
    dsimp only
    rw [Function.update_self, Function.update_idem, Option.getD_some, hr,
      ← FinTM.bufferTape_append]
  have h3 := xr_back_run (xr_extendTM K r) r none
    (fun b inp w s hs => by simp [xr_extendTM, hs]) (fun b inp w hw => by simp [xr_extendTM, hw])
    true 0 u.length
    ⟨some (.back true), d.inputPos, Function.update d.workTapes r (FinTM.bufferTape (u ++ [false])),
      Function.update d.workTapePos r ((u.length : ℤ) + -1), d.output⟩ rfl
    (by dsimp only; rw [Function.update_self]; ring)
    (by
      intro i hi
      dsimp only
      rw [Function.update_self, zero_add, FinTM.bufferTape_nat, ne_eq, List.getElem?_eq_none_iff]
      simp only [List.length_append, List.length_singleton]
      omega)
    (by dsimp only; rw [Function.update_self]; simp)
  have hsplit : (xr_extendTM K r).runFrom d (2 * u.length + 2) =
      (xr_extendTM K r).runFrom ((xr_extendTM K r).step ((xr_extendTM K r).runFrom d u.length))
        (u.length + 1) := by
    rw [show 2 * u.length + 2 = (u.length + 1) + (u.length + 1) by ring,
      MultiTapeTM.runFrom_add, ← MultiTapeTM.runFrom_succ_eq_step']
  rw [hsplit, h1, h2, h3]
  dsimp only
  simp only [Function.update_self, Function.update_idem]
  congr 1
  refine congrArg (Function.update d.workTapes r) (funext fun p => ?_)
  dsimp only
  simp only [Option.getD_none, ite_self]

/-! #### Buffer-tape facts needed by the rows (from the published equations only) -/

/-- A stored word is blank at every negative cell. -/
private theorem xr_bufferTape_neg (v : List Bool) (p : ℤ) (hp : p < 0) :
    FinTM.bufferTape v p = none := by
  induction v using List.reverseRecOn with
  | nil => rw [FinTM.bufferTape_nil]
  | append_singleton L b ih =>
    rw [FinTM.bufferTape_append, Function.update_of_ne (by omega)]
    exact ih

/-- A stored word is blank at and beyond its length. -/
private theorem xr_bufferTape_ge (v : List Bool) (p : ℤ) (hp : (v.length : ℤ) ≤ p) :
    FinTM.bufferTape v p = none := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
  rw [FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
  omega

/-- A stored word is blank exactly off `[0, |v|)`. -/
private theorem xr_bufferTape_eq_none_iff (v : List Bool) (p : ℤ) :
    FinTM.bufferTape v p = none ↔ p < 0 ∨ (v.length : ℤ) ≤ p := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, p = n := ⟨p.toNat, by omega⟩
    rw [FinTM.bufferTape_nat, List.getElem?_eq_none_iff] at h
    omega
  · rintro (h | h)
    · exact xr_bufferTape_neg v p h
    · exact xr_bufferTape_ge v p h

/-- A stored word is non-blank on `[0, |v|)`. -/
private theorem xr_bufferTape_ne_none (v : List Bool) (i : ℕ) (hi : i < v.length) :
    FinTM.bufferTape v i ≠ none := by
  rw [ne_eq, xr_bufferTape_eq_none_iff]
  omega

/-- Blanking the last symbol of a stored word stores its prefix. -/
private theorem xr_bufferTape_pop (L : List Bool) (b : Bool) :
    Function.update (FinTM.bufferTape (L ++ [b])) (L.length : ℤ) none = FinTM.bufferTape L := by
  rw [FinTM.bufferTape_append, Function.update_idem, Function.update_eq_self_iff,
    FinTM.bufferTape_nat]
  exact (List.getElem?_eq_none_iff.mpr le_rfl).symm

/-- The return pass over a stored word with the blanking write clears it entirely. -/
private theorem xr_clear_fun (v : List Bool) :
    (fun p : ℤ => if 0 ≤ p ∧ p < 0 + (v.length : ℤ) then (some none).getD (FinTM.bufferTape v p)
      else FinTM.bufferTape v p) = fun _ => none := by
  funext p
  split_ifs with h
  · rfl
  · rw [xr_bufferTape_eq_none_iff]
    omega

/-! #### The pass, the capture test, the input rewind and the answer -/

/-- **The pass** (the window clear's engine). While the ruler tape `r` reads a symbol, blank the
cell under head `j`, move `j` by `dir` and `r` right; at the ruler's blank, blank once more under
`j` without moving it and start the ruler's return; return the ruler head to its origin. -/
private def xr_passTM (K : ℕ) (j r : Fin K) (dir : SignType) : MultiTapeTM K Bool xr_St where
  q₀ := .run
  tr := fun q _ w =>
    match q with
    | .run =>
      match w r with
      | some _ => xr_act (xr_mv2 j r (some none) dir SignType.pos) (some .run)
      | none => xr_act (xr_mv2 j r (some none) 0 SignType.neg) (some (.back true))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r none SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- The pass's forward phase: after `m ≤ |u|` steps, head `j` has moved `m` cells along `dir`,
blanking the cells it left, and the ruler head is at `m`. -/
private theorem xr_pass_fwd {K : ℕ} {x : List Bool} (j r : Fin K) (hjr : j ≠ r) (dir : SignType)
    (u : List Bool) (d : Cfg K Bool xr_St x) (hd : d.state = some .run)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = 0) (m : ℕ)
    (hm : m ≤ u.length) :
    ∃ f : ℤ → Option Bool,
      (xr_passTM K j r dir).runFrom d m =
        ⟨some .run, d.inputPos, Function.update d.workTapes j f,
          fun i => if i = j then d.workTapePos j + m * (dir : ℤ)
            else if i = r then (m : ℤ) else d.workTapePos i, d.output⟩ ∧
      (∀ p : ℤ, (∃ i : ℕ, i < m ∧ p = d.workTapePos j + i * (dir : ℤ)) → f p = none) ∧
      (∀ p : ℤ, (∀ i : ℕ, i < m → p ≠ d.workTapePos j + i * (dir : ℤ)) →
        f p = d.workTapes j p) := by
  induction m with
  | zero =>
    refine ⟨d.workTapes j, ?_, fun p ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i), fun p _ => rfl⟩
    rw [MultiTapeTM.runFrom_zero]
    apply Cfg.ext
    · exact hd
    · rfl
    · exact (Function.update_eq_self _ _).symm
    · funext i
      dsimp only
      by_cases hij : i = j
      · rw [if_pos hij, hij]
        simp
      · rw [if_neg hij]
        by_cases hir : i = r
        · rw [if_pos hir, hir, hpos]
          simp
        · rw [if_neg hir]
    · rfl
  | succ m ih =>
    obtain ⟨f, hrun, hblank, hkeep⟩ := ih (by omega)
    have hread : (⟨some .run, d.inputPos, Function.update d.workTapes j f,
        fun i => if i = j then d.workTapePos j + m * (dir : ℤ)
          else if i = r then (m : ℤ) else d.workTapePos i, d.output⟩ :
        Cfg K Bool xr_St x).workTapeSymbols r = some (u[m]'(by omega)) := by
      rw [Cfg.workTapeSymbols_eq]
      dsimp only
      rw [if_neg (Ne.symm hjr), if_pos rfl, Function.update_of_ne (Ne.symm hjr), hr,
        FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega)]
    refine ⟨Function.update f (d.workTapePos j + m * (dir : ℤ)) none, ?_, ?_, ?_⟩
    · rw [MultiTapeTM.runFrom_succ_eq_step', hrun, MultiTapeTM.step_of_some rfl,
        show (xr_passTM K j r dir).tr .run _ _ =
          xr_act (xr_mv2 j r (some none) dir SignType.pos) (some .run) by
            simp only [xr_passTM]
            rw [hread],
        xr_mv2_apply j r hjr]
      dsimp only
      simp only [Function.update_self, Function.update_idem, Option.getD_some,
        if_neg (Ne.symm hjr), xr_cast_pos, ite_true]
      congr 1
      funext i
      by_cases hij : i = j
      · simp only [if_pos hij]
        push_cast
        ring
      · by_cases hir : i = r
        · simp only [if_neg hij, if_pos hir]
          push_cast
          ring
        · simp only [if_neg hij, if_neg hir]
    · rintro p ⟨i, hi, rfl⟩
      by_cases hp : d.workTapePos j + i * (dir : ℤ) = d.workTapePos j + m * (dir : ℤ)
      · rw [hp, Function.update_self]
      · rw [Function.update_of_ne hp]
        refine hblank _ ⟨i, ?_, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · exact h
        · exact absurd (by rw [h]) hp
    · intro p hp
      rw [Function.update_of_ne (hp m (by omega))]
      exact hkeep p (fun i hi => hp i (by omega))

/-- **The pass's contract.** From the origin of the ruler word `u`, `2|u| + 2` steps move head `j`
by `|u|` cells along `dir`, blank the `|u| + 1` cells it visited, return the ruler head to `0`,
change nothing else, and stop at `done true`.

**Proof sketch.** `xr_pass_fwd` gives the first `|u|` steps: head `j` moves `|u|` cells along
`dir`, blanking each cell it leaves, while the ruler head walks over `u`. At the ruler's right
blank one step blanks the last visited cell and turns the ruler head back, and `xr_back_run`
returns it to `0` in `|u| + 1` steps. The visited cells are `pos + i·dir` for `i ≤ |u|`; every
other cell keeps its symbol. -/
private theorem xr_passTM_run {K : ℕ} {x : List Bool} (j r : Fin K) (hjr : j ≠ r) (dir : SignType)
    (u : List Bool) (d : Cfg K Bool xr_St x) (hd : d.state = some .run)
    (hr : d.workTapes r = FinTM.bufferTape u) (hpos : d.workTapePos r = 0) :
    ∃ f : ℤ → Option Bool,
      (xr_passTM K j r dir).runFrom d (2 * u.length + 2) =
        ⟨some (.done true), d.inputPos, Function.update d.workTapes j f,
          Function.update d.workTapePos j (d.workTapePos j + u.length * (dir : ℤ)), d.output⟩ ∧
      (∀ p : ℤ, (∃ i : ℕ, i ≤ u.length ∧ p = d.workTapePos j + i * (dir : ℤ)) → f p = none) ∧
      (∀ p : ℤ, (∀ i : ℕ, i ≤ u.length → p ≠ d.workTapePos j + i * (dir : ℤ)) →
        f p = d.workTapes j p) := by
  obtain ⟨f, hrun, hblank, hkeep⟩ := xr_pass_fwd j r hjr dir u d hd hr hpos u.length le_rfl
  set c₁ : Cfg K Bool xr_St x := ⟨some .run, d.inputPos, Function.update d.workTapes j f,
    fun i => if i = j then d.workTapePos j + u.length * (dir : ℤ)
      else if i = r then (u.length : ℤ) else d.workTapePos i, d.output⟩ with hc₁
  have hread : c₁.workTapeSymbols r = none := by
    rw [Cfg.workTapeSymbols_eq, hc₁]
    dsimp only
    rw [if_neg (Ne.symm hjr), if_pos rfl, Function.update_of_ne (Ne.symm hjr), hr,
      FinTM.bufferTape_nat, List.getElem?_eq_none_iff]
  set f' : ℤ → Option Bool := Function.update f (d.workTapePos j + u.length * (dir : ℤ)) none
    with hf'
  have h2 : (xr_passTM K j r dir).step c₁ =
      ⟨some (.back true), d.inputPos, Function.update d.workTapes j f',
        fun i => if i = j then d.workTapePos j + u.length * (dir : ℤ)
          else if i = r then (u.length : ℤ) + -1 else d.workTapePos i, d.output⟩ := by
    rw [MultiTapeTM.step_of_some rfl,
      show (xr_passTM K j r dir).tr .run _ _ =
        xr_act (xr_mv2 j r (some none) 0 SignType.neg) (some (.back true)) by
          simp only [xr_passTM]
          rw [hread],
      xr_mv2_apply j r hjr, hc₁]
    dsimp only
    simp only [Function.update_self, Function.update_idem, Option.getD_some,
      if_neg (Ne.symm hjr), SignType.coe_zero, add_zero, ite_true]
    congr 1
    funext i
    by_cases hij : i = j
    · simp [hij]
    · by_cases hir : i = r
      · simp [hir]
      · simp [hij, hir]
  have h3 := xr_back_run (xr_passTM K j r dir) r none
    (fun b inp w s hs => by simp [xr_passTM, hs]) (fun b inp w hw => by simp [xr_passTM, hw])
    true 0 u.length
    ⟨some (.back true), d.inputPos, Function.update d.workTapes j f',
      fun i => if i = j then d.workTapePos j + u.length * (dir : ℤ)
        else if i = r then (u.length : ℤ) + -1 else d.workTapePos i, d.output⟩ rfl
    (by dsimp only; rw [if_neg (Ne.symm hjr), if_pos rfl]; ring)
    (by
      intro i hi
      dsimp only
      rw [Function.update_of_ne (Ne.symm hjr), zero_add, hr]
      exact xr_bufferTape_ne_none u i hi)
    (by
      dsimp only
      rw [Function.update_of_ne (Ne.symm hjr), hr]
      exact xr_bufferTape_neg u _ (by omega))
  refine ⟨f', ?_, ?_, ?_⟩
  · have hsplit : (xr_passTM K j r dir).runFrom d (2 * u.length + 2) =
        (xr_passTM K j r dir).runFrom
          ((xr_passTM K j r dir).step ((xr_passTM K j r dir).runFrom d u.length))
          (u.length + 1) := by
      rw [show 2 * u.length + 2 = (u.length + 1) + (u.length + 1) by ring,
        MultiTapeTM.runFrom_add, ← MultiTapeTM.runFrom_succ_eq_step']
    rw [hsplit, hrun, h2, h3]
    dsimp only
    congr 1
    · have hG : Function.update (Function.update d.workTapes j f') r
          (fun p => if 0 ≤ p ∧ p < 0 + (u.length : ℤ)
            then none.getD (Function.update d.workTapes j f' r p)
            else Function.update d.workTapes j f' r p) = Function.update d.workTapes j f' := by
        rw [Function.update_eq_self_iff, Function.update_of_ne (Ne.symm hjr)]
        funext p
        simp only [Option.getD_none, ite_self]
      exact hG
    · funext i
      by_cases hij : i = j
      · rw [hij, Function.update_of_ne hjr, if_pos rfl, Function.update_self]
      · by_cases hir : i = r
        · rw [hir, Function.update_self, Function.update_of_ne (Ne.symm hjr), hpos]
        · rw [Function.update_of_ne hir, if_neg hij, if_neg hir, Function.update_of_ne hij]
  · rintro p ⟨i, hi, rfl⟩
    by_cases hp : d.workTapePos j + i * (dir : ℤ) = d.workTapePos j + u.length * (dir : ℤ)
    · rw [hp, hf', Function.update_self]
    · rw [hf', Function.update_of_ne hp]
      refine hblank _ ⟨i, ?_, rfl⟩
      rcases Nat.lt_or_eq_of_le hi with h | h
      · exact h
      · exact absurd (by rw [h]) hp
  · intro p hp
    rw [hf', Function.update_of_ne (hp u.length le_rfl)]
    exact hkeep p (fun i hi => hp i hi.le)

/-- **The capture test.** From the end of the captured output, step left and read the last symbol:
blank (an empty output) exits `done false`; `true` steps left once more and exits `done true` at
a blank there (the output was exactly `[true]`); anything else exits `done false`. Every exit
clears the captured output and returns the head to its origin. -/
private def xr_testTM (K : ℕ) (r : Fin K) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q _ w =>
    match q with
    | .start => xr_act (xr_mv1 r none SignType.neg) (some .run)
    | .run =>
      match w r with
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done false))
      | some true => xr_act (xr_mv1 r (some none) SignType.neg) (some .aux)
      | some false => xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false))
    | .aux =>
      match w r with
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done true))
      | some _ => xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false))
    | .back b =>
      match w r with
      | some _ => xr_act (xr_mv1 r (some none) SignType.neg) (some (.back b))
      | none => xr_act (xr_mv1 r none SignType.pos) (some (.done b))
    | q => xr_stay q

/-- The test's clearing tail: from `back false` at the end of the stored word `v`, `|v| + 1` steps
blank it, return the head to `0`, and stop at `done false`. -/
private theorem xr_test_tail {K : ℕ} {x : List Bool} (r : Fin K) (v : List Bool)
    (d : Cfg K Bool xr_St x) (hd : d.state = some (.back false))
    (hr : d.workTapes r = FinTM.bufferTape v) (hpos : d.workTapePos r = (v.length : ℤ) - 1) :
    (xr_testTM K r).runFrom d (v.length + 1) =
      ⟨some (.done false), d.inputPos, Function.update d.workTapes r (fun _ => none),
        Function.update d.workTapePos r 0, d.output⟩ := by
  rw [xr_back_run (xr_testTM K r) r (some none)
    (fun b inp w s hs => by simp [xr_testTM, hs]) (fun b inp w hw => by simp [xr_testTM, hw])
    false 0 v.length d hd (by rw [hpos]; ring)
    (fun i hi => by rw [zero_add, hr]; exact xr_bufferTape_ne_none v i hi)
    (by rw [hr]; exact xr_bufferTape_neg v _ (by omega)), hr, xr_clear_fun]

/-- **The capture test's contract.** With the output `out` stored at the origin and the head at
its end, `|out| + 2` steps clear it, return the head to `0`, change nothing else, and stop at
`done true` exactly when `out = [true]`.

**Proof sketch.** One step left onto the output's last cell. If the output is empty, that cell
is blank and one step right exits `done false` (two steps). Otherwise write it as `L ++ [b]`;
blank `b` and step left. For `b = false`, the clearing tail `xr_test_tail` blanks `L`, returns
the head to `0` and exits `done false`. For `b = true`, the next read decides: a blank (the
output was `[true]`) exits `done true` one step right, and a symbol is blanked and the clearing
tail exits `done false`. Every case takes `|out| + 2` steps. -/
private theorem xr_testTM_run {K : ℕ} {x : List Bool} (r : Fin K) (out : List Bool)
    (d : Cfg K Bool xr_St x) (hd : d.state = some .start)
    (hr : d.workTapes r = FinTM.bufferTape out) (hpos : d.workTapePos r = out.length) :
    (xr_testTM K r).runFrom d (out.length + 2) =
      ⟨some (.done (decide (out = [true]))), d.inputPos,
        Function.update d.workTapes r (fun _ => none), Function.update d.workTapePos r 0,
        d.output⟩ := by
  have hstart : (xr_testTM K r).step d = ⟨some .run, d.inputPos, d.workTapes,
      Function.update d.workTapePos r ((out.length : ℤ) + -1), d.output⟩ := by
    rw [MultiTapeTM.step_of_some hd,
      show (xr_testTM K r).tr .start _ _ = xr_act (xr_mv1 r none SignType.neg) (some .run)
        from rfl, xr_mv1_apply_none, xr_cast_neg, hpos]
  rcases List.eq_nil_or_concat out with rfl | ⟨L, b, hout⟩
  · -- the empty output: two steps
    have hdec : decide (([] : List Bool) = [true]) = false := rfl
    have hread : (⟨some .run, d.inputPos, d.workTapes,
        Function.update d.workTapePos r ((([] : List Bool).length : ℤ) + -1), d.output⟩ :
        Cfg K Bool xr_St x).workTapeSymbols r = none := by
      rw [Cfg.workTapeSymbols_eq]
      dsimp only
      rw [Function.update_self, hr, FinTM.bufferTape_nil]
    rw [show ([] : List Bool).length + 2 = 2 from rfl, xr_runFrom_two, hstart,
      MultiTapeTM.step_of_some rfl,
      show (xr_testTM K r).tr .run _ _ = xr_act (xr_mv1 r none SignType.pos) (some (.done false))
        by simp only [xr_testTM]; rw [hread],
      xr_mv1_apply_none, hdec]
    dsimp only
    rw [Function.update_self, Function.update_idem, xr_cast_pos]
    apply Cfg.ext
    · rfl
    · rfl
    · symm
      rw [Function.update_eq_self_iff, hr, FinTM.bufferTape_nil]
    · simp
    · rfl
  · -- a non-empty output `L ++ [b]`: the first read sees `b`
    rw [List.concat_eq_append] at hout
    subst hout
    have hlen : (L ++ [b]).length = L.length + 1 := by simp
    have hread : (⟨some .run, d.inputPos, d.workTapes,
        Function.update d.workTapePos r (((L ++ [b]).length : ℤ) + -1), d.output⟩ :
        Cfg K Bool xr_St x).workTapeSymbols r = some b := by
      rw [Cfg.workTapeSymbols_eq]
      dsimp only
      rw [Function.update_self, hr, hlen, FinTM.bufferTape_append]
      push_cast
      rw [add_neg_cancel_right, Function.update_self]
    rcases b with _ | _
    · -- last symbol `false`: blank it and clear the rest
      have hstep2 : (xr_testTM K r).step ⟨some .run, d.inputPos, d.workTapes,
          Function.update d.workTapePos r (((L ++ [false]).length : ℤ) + -1), d.output⟩ =
          ⟨some (.back false), d.inputPos, Function.update d.workTapes r (FinTM.bufferTape L),
            Function.update d.workTapePos r ((L.length : ℤ) - 1), d.output⟩ := by
        rw [MultiTapeTM.step_of_some rfl,
          show (xr_testTM K r).tr .run _ _ =
            xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false)) by
              simp only [xr_testTM]; rw [hread],
          xr_mv1_apply, xr_cast_neg]
        dsimp only
        rw [Function.update_self, Function.update_idem, Option.getD_some, hr, hlen]
        congr 1
        · congr 1
          push_cast
          rw [add_neg_cancel_right, xr_bufferTape_pop]
        · congr 1
          push_cast
          ring
      have hdec : decide (L ++ [false] = [true]) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        have := List.append_inj_right' (h.trans (List.nil_append [true]).symm) rfl
        simp at this
      rw [hlen, show L.length + 1 + 2 = 2 + (L.length + 1) by omega,
        MultiTapeTM.runFrom_add (tm := xr_testTM K r) d 2 (L.length + 1), xr_runFrom_two, hstart,
        hstep2, xr_test_tail r L _ rfl (by dsimp only; rw [Function.update_self])
          (by dsimp only; rw [Function.update_self]), hdec]
      dsimp only
      rw [Function.update_idem, Function.update_idem]
    · -- last symbol `true`: blank it, then look at the symbol before it
      have hstep2 : (xr_testTM K r).step ⟨some .run, d.inputPos, d.workTapes,
          Function.update d.workTapePos r (((L ++ [true]).length : ℤ) + -1), d.output⟩ =
          ⟨some .aux, d.inputPos, Function.update d.workTapes r (FinTM.bufferTape L),
            Function.update d.workTapePos r ((L.length : ℤ) - 1), d.output⟩ := by
        rw [MultiTapeTM.step_of_some rfl,
          show (xr_testTM K r).tr .run _ _ =
            xr_act (xr_mv1 r (some none) SignType.neg) (some .aux) by
              simp only [xr_testTM]; rw [hread],
          xr_mv1_apply, xr_cast_neg]
        dsimp only
        rw [Function.update_self, Function.update_idem, Option.getD_some, hr, hlen]
        congr 1
        · congr 1
          push_cast
          rw [add_neg_cancel_right, xr_bufferTape_pop]
        · congr 1
          push_cast
          ring
      rcases List.eq_nil_or_concat L with rfl | ⟨L', b', hL⟩
      · -- the output was `[true]`
        have hdec : decide (([] : List Bool) ++ [true] = [true]) = true := rfl
        have hread3 : (⟨some .aux, d.inputPos, Function.update d.workTapes r (FinTM.bufferTape []),
            Function.update d.workTapePos r ((([] : List Bool).length : ℤ) - 1), d.output⟩ :
            Cfg K Bool xr_St x).workTapeSymbols r = none := by
          rw [Cfg.workTapeSymbols_eq]
          dsimp only
          rw [Function.update_self, Function.update_self, FinTM.bufferTape_nil]
        rw [show (([] : List Bool) ++ [true]).length + 2 = 2 + 1 from rfl,
          MultiTapeTM.runFrom_add (tm := xr_testTM K r) d 2 1, xr_runFrom_two, xr_runFrom_one,
          hstart, hstep2, MultiTapeTM.step_of_some rfl,
          show (xr_testTM K r).tr .aux _ _ =
            xr_act (xr_mv1 r none SignType.pos) (some (.done true)) by
              simp only [xr_testTM]; rw [hread3],
          xr_mv1_apply_none, xr_cast_pos, hdec]
        dsimp only
        rw [Function.update_self, Function.update_idem, FinTM.bufferTape_nil]
        apply Cfg.ext
        · rfl
        · rfl
        · rfl
        · simp
        · rfl
      · -- an output of length at least two
        rw [List.concat_eq_append] at hL
        subst hL
        have hlen' : (L' ++ [b']).length = L'.length + 1 := by simp
        have hread3 : (⟨some .aux, d.inputPos,
            Function.update d.workTapes r (FinTM.bufferTape (L' ++ [b'])),
            Function.update d.workTapePos r (((L' ++ [b']).length : ℤ) - 1), d.output⟩ :
            Cfg K Bool xr_St x).workTapeSymbols r = some b' := by
          rw [Cfg.workTapeSymbols_eq]
          dsimp only
          rw [Function.update_self, Function.update_self, hlen', FinTM.bufferTape_append]
          push_cast
          rw [add_sub_cancel_right, Function.update_self]
        have hstep3 : (xr_testTM K r).step ⟨some .aux, d.inputPos,
            Function.update d.workTapes r (FinTM.bufferTape (L' ++ [b'])),
            Function.update d.workTapePos r (((L' ++ [b']).length : ℤ) - 1), d.output⟩ =
            ⟨some (.back false), d.inputPos, Function.update d.workTapes r (FinTM.bufferTape L'),
              Function.update d.workTapePos r ((L'.length : ℤ) - 1), d.output⟩ := by
          rw [MultiTapeTM.step_of_some rfl,
            show (xr_testTM K r).tr .aux _ _ =
              xr_act (xr_mv1 r (some none) SignType.neg) (some (.back false)) by
                simp only [xr_testTM]; rw [hread3],
            xr_mv1_apply, xr_cast_neg]
          dsimp only
          rw [Function.update_self, Function.update_self, Function.update_idem,
            Function.update_idem, Option.getD_some, hlen']
          congr 1
          · congr 1
            push_cast
            rw [add_sub_cancel_right, xr_bufferTape_pop]
          · congr 1
            push_cast
            ring
        have hdec : decide (L' ++ [b'] ++ [true] = [true]) = false := by
          rw [decide_eq_false_iff_not]
          intro h
          have := congrArg List.length h
          simp at this
        rw [show (L' ++ [b'] ++ [true]).length + 2 = 2 + 1 + (L'.length + 1) by
            simp only [List.length_append, List.length_singleton]; try omega,
          MultiTapeTM.runFrom_add (tm := xr_testTM K r) d (2 + 1) (L'.length + 1),
          MultiTapeTM.runFrom_add (tm := xr_testTM K r) d 2 1, xr_runFrom_two, xr_runFrom_one,
          hstart, hstep2, hstep3,
          xr_test_tail r L' _ rfl (by dsimp only; rw [Function.update_self])
            (by dsimp only; rw [Function.update_self]), hdec]
        dsimp only
        rw [Function.update_idem, Function.update_idem]

/-- **The input rewind**: a left step, then left while the input head reads a symbol, then one
step right at the left blank. -/
private def xr_inRewindTM (K : ℕ) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q inp _ =>
    match q with
    | .start => FinTM.controlAction .neg (some .run)
    | .run =>
      match inp with
      | some _ => FinTM.controlAction .neg (some .run)
      | none => FinTM.controlAction .pos (some (.done true))
    | q => xr_stay q

/-- **The answer**: emit `b` and halt. -/
private def xr_answerTM (K : ℕ) (b : Bool) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun _ _ _ => ⟨0, fun _ => (none, 0), some b, none⟩

/-- The answer's contract: one step from any live state emits `b` and halts. -/
private theorem xr_answerTM_run {K : ℕ} {x : List Bool} (b : Bool) (d : Cfg K Bool xr_St x)
    (q : xr_St) (hd : d.state = some q) :
    (xr_answerTM K b).runFrom d 1 = {d with state := none, output := d.output ++ [b]} := by
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero, MultiTapeTM.step_of_some hd]
  apply Cfg.ext
  · exact Action.apply_state _ _
  · exact (Action.apply_inputPos _ _).trans (moveInputPos_zero _)
  · funext i
    rw [Action.apply_workTapes, Cfg.workTapeSymbols_eq]
    simp [xr_answerTM]
  · funext i
    rw [Action.apply_workTapePos]
    simp [xr_answerTM]
  · exact Action.apply_output _ _

/-! #### The clocked replay and its silent embedding

The step clock over the replay machine, as `Turing.exists_stepClockTMVia` supplies it, read at
`Γ = Bool` with the identity embedding and no stop state; the tape bank of `E` (the clocked
replay's `k + 2` tapes, then the capture tape and the depth tape); and one replay's two exits,
identified with `N`'s branch along the choice word through the replay lemma and the translation
of the work tapes. -/

/-- **The step clock over the replay machine.** The control `Q`, the clocked machine `H` on
`N.k + 2` tapes (the counter last), the injection of the replay's states, the two exit families,
and the clock's two exits: `finish none` when the body halts within the budget, `timeout` with
the body's live state when it does not, each with no earlier exit. -/
private structure xr_Clock (N : FinNDTM Bool) where
  Q : Type
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  H : MultiTapeTM (N.k + 2) Bool Q
  inj : N.State → Q
  finish : Option N.State → Q
  timeout : Option N.State → Q
  finish_ne_timeout : ∀ a b, finish a ≠ timeout b
  inj_ne : ∀ s r, inj s ≠ finish r ∧ inj s ≠ timeout r
  spec_finish : ∀ {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x) (q : N.State),
    c.state = some q → ∀ (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ),
    (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p) →
    ∀ τ ≤ Nat.ofDigits 2 (w.map Bool.toNat), (N.tm.replayTM.runFrom c τ).state = none →
    (∀ u < τ, (N.tm.replayTM.runFrom c u).state ≠ none) →
    ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ w' : List Bool, w'.length = w.length ∧
      H.runFrom (clockCfg (some (inj q)) c ct cp) T =
        clockCfg (some (finish none)) (N.tm.replayTM.runFrom c τ) (wordPatch ct cp w') cp ∧
      ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
        (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)
  spec_timeout : ∀ {x : List Bool} (c : Cfg (N.k + 1) Bool N.State x) (q : N.State),
    c.state = some q → ∀ (w : List Bool) (ct : ℤ → Option Bool) (cp : ℤ),
    (∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape w p) →
    (∀ u ≤ Nat.ofDigits 2 (w.map Bool.toNat), (N.tm.replayTM.runFrom c u).state ≠ none) →
    ∃ T ≤ 5 * Nat.ofDigits 2 (w.map Bool.toNat) + 2 * w.length + 2, ∃ w' : List Bool,
      w'.length = w.length ∧
      H.runFrom (clockCfg (some (inj q)) c ct cp) T =
        clockCfg (some (timeout
            (N.tm.replayTM.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))).state))
          (N.tm.replayTM.runFrom c (Nat.ofDigits 2 (w.map Bool.toNat))) (wordPatch ct cp w') cp ∧
      ∀ u < T, ∀ r, (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (finish r) ∧
        (H.runFrom (clockCfg (some (inj q)) c ct cp) u).state ≠ some (timeout r)

attribute [instance] xr_Clock.fintypeQ xr_Clock.decEqQ

/-- With no stop state, a body configuration is stopped exactly when it is halted. -/
private theorem xr_stopped_iff {k : ℕ} {S : Type} {x : List Bool} (c : Cfg k Bool S x) :
    c.Stopped (fun _ : S => false) ↔ c.state = none := by
  rw [Cfg.stopped_iff]
  simp

/-- The clock exists: `Turing.exists_stepClockTMVia` at `Γ = Bool`, the identity embedding and
no stop state, with its two exits read. -/
private theorem xr_Clock.exists (N : FinNDTM Bool) : Nonempty (xr_Clock N) := by
  obtain ⟨Q, instF, instD, H, inj, finish, timeout, -, -, hft, hinj, hspec⟩ :=
    exists_stepClockTMVia (Function.Embedding.refl Bool) N.tm.replayTM (fun _ => false)
  have hmap : ∀ w : List Bool, w.map ⇑(Function.Embedding.refl Bool) = w := fun w => by
    rw [Function.Embedding.coe_refl, List.map_id]
  letI : Fintype Q := instF
  letI : DecidableEq Q := instD
  refine ⟨⟨Q, H, inj, finish, timeout, hft, hinj, ?_, ?_⟩⟩
  · intro x c q hq w ct cp hct τ hτ hstop hlive
    have hct' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        ct (cp + p) = FinTM.bufferTape (w.map ⇑(Function.Embedding.refl Bool)) p := by
      rw [hmap]; exact hct
    obtain ⟨T, hT, w', hw', hrun, hguard, -⟩ := (hspec c q hq w ct cp hct').1 τ hτ
      ((xr_stopped_iff _).mpr hstop)
      (fun u hu => by rw [xr_stopped_iff]; exact hlive u hu)
    refine ⟨T, hT, w', hw', ?_, hguard⟩
    rw [hrun, hstop, hmap]
  · intro x c q hq w ct cp hct hlive
    have hct' : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
        ct (cp + p) = FinTM.bufferTape (w.map ⇑(Function.Embedding.refl Bool)) p := by
      rw [hmap]; exact hct
    obtain ⟨T, hT, w', hw', hrun, hguard, -⟩ := (hspec c q hq w ct cp hct').2
      (fun u hu => by rw [xr_stopped_iff]; exact hlive u hu)
    refine ⟨T, hT, w', hw', ?_, hguard⟩
    rw [hrun, hmap]

/-! The tape bank of `E` for an NDTM with `k` work tapes: the `k + 2` tapes of the clocked replay
(`N`'s `k` tapes, the choice tape, the clock's counter), then the capture tape and the depth
tape, as `Fin (k + 2 + 2)`. -/

/-- The clocked replay's bank, as the first `k + 2` tapes. -/
private def xr_ι (k : ℕ) : Fin (k + 2) ↪ Fin (k + 2 + 2) := Fin.castAddEmb 2

/-- The capture tape. -/
private def xr_cap (k : ℕ) : Fin (k + 2 + 2) := Fin.natAdd (k + 2) 0

/-- The depth tape. -/
private def xr_dep (k : ℕ) : Fin (k + 2 + 2) := Fin.natAdd (k + 2) 1

/-- `N`'s work tape `j`. -/
private def xr_work (k : ℕ) (j : Fin k) : Fin (k + 2 + 2) := Fin.castAdd 2 j.castSucc.castSucc

/-- The choice tape. -/
private def xr_choice (k : ℕ) : Fin (k + 2 + 2) := Fin.castAdd 2 (Fin.last k).castSucc

/-- The clock's counter tape. -/
private def xr_ctr (k : ℕ) : Fin (k + 2 + 2) := Fin.castAdd 2 (Fin.last (k + 1))

/-- `E`'s work tapes from their five banks. -/
private def xr_tapes {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp : ℤ → Option Bool) :
    Fin (k + 2 + 2) → ℤ → Option Bool :=
  Fin.addCases (Fin.lastCases ctr (Fin.lastCases ch wk))
    (fun j : Fin 2 => if j = 0 then cp else dp)

/-- `E`'s work heads from their five banks. -/
private def xr_heads {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) : Fin (k + 2 + 2) → ℤ :=
  Fin.addCases (Fin.lastCases hctr (Fin.lastCases hch hk))
    (fun j : Fin 2 => if j = 0 then hcp else hdp)

private theorem xr_tapes_work {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) (j : Fin k) :
    xr_tapes wk ch ctr cp dp (xr_work k j) = wk j := by
  simp [xr_tapes, xr_work]

private theorem xr_tapes_choice {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_choice k) = ch := by
  simp [xr_tapes, xr_choice]

private theorem xr_tapes_ctr {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_ctr k) = ctr := by
  simp [xr_tapes, xr_ctr]

private theorem xr_tapes_cap {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_cap k) = cp := by
  simp [xr_tapes, xr_cap]

private theorem xr_tapes_dep {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) :
    xr_tapes wk ch ctr cp dp (xr_dep k) = dp := by
  simp [xr_tapes, xr_dep]

private theorem xr_heads_work {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (j : Fin k) :
    xr_heads hk hch hctr hcp hdp (xr_work k j) = hk j := by
  simp [xr_heads, xr_work]

private theorem xr_heads_choice {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_choice k) = hch := by
  simp [xr_heads, xr_choice]

private theorem xr_heads_ctr {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_ctr k) = hctr := by
  simp [xr_heads, xr_ctr]

private theorem xr_heads_cap {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_cap k) = hcp := by
  simp [xr_heads, xr_cap]

private theorem xr_heads_dep {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) :
    xr_heads hk hch hctr hcp hdp (xr_dep k) = hdp := by
  simp [xr_heads, xr_dep]

/-- The capture tape is outside the clocked replay's bank. -/
private theorem xr_cap_not_mem (k : ℕ) : xr_cap k ∉ Set.range (xr_ι k) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp [xr_ι, xr_cap] at this
  omega

/-- The depth tape is outside the clocked replay's bank. -/
private theorem xr_dep_not_mem (k : ℕ) : xr_dep k ∉ Set.range (xr_ι k) := by
  rintro ⟨i, hi⟩
  have := congrArg Fin.val hi
  simp [xr_ι, xr_dep] at this
  omega

private theorem xr_dep_ne_cap (k : ℕ) : xr_dep k ≠ xr_cap k := by
  intro h
  have := congrArg Fin.val h
  simp [xr_dep, xr_cap] at this

/-- Every index of `Fin (m + n)` is a left or a right index. -/
private theorem xr_addCases_split {m n : ℕ} (j : Fin (m + n)) :
    (∃ i : Fin m, j = Fin.castAdd n i) ∨ ∃ i : Fin n, j = Fin.natAdd m i :=
  Fin.addCases
    (motive := fun j => (∃ i : Fin m, j = Fin.castAdd n i) ∨ ∃ i : Fin n, j = Fin.natAdd m i)
    (fun i => Or.inl ⟨i, rfl⟩) (fun i => Or.inr ⟨i, rfl⟩) j

/-- Every index of `Fin (n + 1)` is the last one or a cast. -/
private theorem xr_lastCases_split {n : ℕ} (i : Fin (n + 1)) :
    i = Fin.last n ∨ ∃ i' : Fin n, i = i'.castSucc :=
  Fin.lastCases (motive := fun i => i = Fin.last n ∨ ∃ i' : Fin n, i = i'.castSucc)
    (Or.inl rfl) (fun i' => Or.inr ⟨i', rfl⟩) i

private theorem xr_fin2 (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- **The embedded clocked configuration, by banks**: the clocked replay configuration over `N`'s
configuration `c`, the choice tape and the counter, embedded silently with the capture tape and
the depth tape, is the explicit `E` configuration. -/
private theorem xr_embed_eq {k : ℕ} {S Q : Type} {z : List Bool} (q : Option Q)
    (c : Cfg k Bool S z) (chT ct : ℤ → Option Bool) (chP cp : ℤ) (dp : ℤ → Option Bool)
    (hdp : ℤ) (pre out₀ : List Bool) :
    embedSilentCfg (xr_ι k) (xr_cap k) (fun _ => dp) (fun _ => hdp) pre out₀
        (clockCfg q (NDTM.withChoiceTape c chT chP) ct cp) =
      ⟨q, c.inputPos, xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp,
        xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp, out₀⟩ := by
  apply Cfg.ext
  · rw [embedSilentCfg_state, clockCfg_state]
  · rw [embedSilentCfg_inputPos, clockCfg_inputPos, NDTM.withChoiceTape_inputPos]
  · funext j
    rcases xr_addCases_split j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [← Fin.castAddEmb_apply, show Fin.castAddEmb 2 = xr_ι k from rfl,
        embedSilentCfg_selected_tape]
      funext a
      rw [clockCfg_workTapes]
      show _ = xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp
        (Fin.castAdd 2 i) a
      rw [xr_tapes, Fin.addCases_left]
      rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
      · rw [Fin.lastCases_last, Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, NDTM.withChoiceTape_workTapes]
    · rcases xr_fin2 i with rfl | rfl
      · rw [show Fin.natAdd (k + 2) (0 : Fin 2) = xr_cap k from rfl,
          (embedSilentCfg_cap _ _ (xr_cap_not_mem k) _ _ _ _ _).1, clockCfg_output,
          NDTM.withChoiceTape_output]
        show _ = xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp
          (Fin.natAdd (k + 2) 0)
        rw [xr_tapes, Fin.addCases_right]
        simp
      · rw [show Fin.natAdd (k + 2) (1 : Fin 2) = xr_dep k from rfl,
          (embedSilentCfg_unselected _ _ _ _ _ _ _ _ (xr_dep_not_mem k) (xr_dep_ne_cap k)).1]
        show _ = xr_tapes c.workTapes chT ct (FinTM.bufferTape (pre ++ c.output)) dp
          (Fin.natAdd (k + 2) 1)
        rw [xr_tapes, Fin.addCases_right]
        simp
  · funext j
    rcases xr_addCases_split j with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · rw [← Fin.castAddEmb_apply, show Fin.castAddEmb 2 = xr_ι k from rfl,
        embedSilentCfg_selected_pos, clockCfg_workTapePos]
      show _ = xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp (Fin.castAdd 2 i)
      rw [xr_heads, Fin.addCases_left]
      rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
      · rw [Fin.lastCases_last, Fin.lastCases_last]
      · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc, NDTM.withChoiceTape_workTapePos]
    · rcases xr_fin2 i with rfl | rfl
      · rw [show Fin.natAdd (k + 2) (0 : Fin 2) = xr_cap k from rfl,
          (embedSilentCfg_cap _ _ (xr_cap_not_mem k) _ _ _ _ _).2, clockCfg_output,
          NDTM.withChoiceTape_output]
        show _ = xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp
          (Fin.natAdd (k + 2) 0)
        rw [xr_heads, Fin.addCases_right]
        simp
      · rw [show Fin.natAdd (k + 2) (1 : Fin 2) = xr_dep k from rfl,
          (embedSilentCfg_unselected _ _ _ _ _ _ _ _ (xr_dep_not_mem k) (xr_dep_ne_cap k)).2]
        show _ = xr_heads c.workTapePos chP cp ((pre ++ c.output).length : ℤ) hdp
          (Fin.natAdd (k + 2) 1)
        rw [xr_heads, Fin.addCases_right]
        simp
  · rw [embedSilentCfg_output]

/-- Patching a same-width word over a stored word at the origin stores the new word. -/
private theorem xr_wordPatch_buffer (w w' : List Bool) (hw : w'.length = w.length) :
    wordPatch (FinTM.bufferTape w) 0 w' = FinTM.bufferTape w' := by
  funext q
  by_cases h : 0 ≤ q ∧ q < 0 + (w'.length : ℤ)
  · rw [wordPatch_of_mem _ _ _ h.1 h.2, sub_zero]
  · rw [wordPatch_of_not_mem _ _ _ h, (xr_bufferTape_eq_none_iff _ _).mpr ?_,
      (xr_bufferTape_eq_none_iff _ _).mpr ?_]
    · omega
    · omega

/-- **The replay phase**: the clocked replay, embedded silently with the capture tape. -/
private def xr_replayTM {N : FinNDTM Bool} (C : xr_Clock N) :
    MultiTapeTM (N.k + 2 + 2) Bool C.Q :=
  embedSilentTM (xr_ι N.k) (xr_cap N.k) C.H

/-- `E` at the start of a replay of the choice word `s` under the budget word `w`: the clock at
the replay's initial state, `N`'s tapes blank with their heads at `h`, the input head at `1`, the
capture tape blank, the depth word `wD`, every auxiliary head at its origin. -/
private def xr_replayStart {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) : Cfg (N.k + 2 + 2) Bool C.Q z :=
  ⟨some (C.inj N.tm.q₀), 1,
    xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape w) (FinTM.bufferTape [])
      (FinTM.bufferTape wD),
    xr_heads h 0 0 0 0, []⟩

/-- The replay's start is the embedded clocked configuration over the translated initial
configuration of `N`. -/
private theorem xr_replayStart_eq {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) :
    xr_replayStart C z s w wD h =
      embedSilentCfg (xr_ι N.k) (xr_cap N.k) (fun _ => FinTM.bufferTape wD) (fun _ => 0) [] []
        (clockCfg (some (C.inj N.tm.q₀))
          (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0)
          (FinTM.bufferTape w) 0) := by
  rw [xr_embed_eq]
  have h1 : (fun i p => (N.tm.initCfg z).workTapes i (p - h i)) =
      fun (_ : Fin N.k) (_ : ℤ) => (none : Option Bool) := by
    funext i p
    rw [NDTM.initCfg_eq, Cfg.init_workTapes]
  have h2 : (fun i => (N.tm.initCfg z).workTapePos i + h i) = h := by
    funext i
    rw [NDTM.initCfg_eq, Cfg.init_workTapePos, zero_add]
  apply Cfg.ext
  · rfl
  · show (1 : Fin _) = (N.tm.initCfg z).inputPos
    rw [NDTM.initCfg_eq, Cfg.init_inputPos]
  · show xr_tapes (fun _ _ => none) _ _ (FinTM.bufferTape []) _ =
      xr_tapes (fun i p => (N.tm.initCfg z).workTapes i (p - h i)) _ _
        (FinTM.bufferTape ([] ++ (N.tm.initCfg z).output)) _
    rw [h1, NDTM.initCfg_eq, Cfg.init_output, List.nil_append]
  · show xr_heads h 0 0 0 0 =
      xr_heads (fun i => (N.tm.initCfg z).workTapePos i + h i) 0 0
        (([] ++ (N.tm.initCfg z).output).length : ℤ) 0
    rw [h2, NDTM.initCfg_eq, Cfg.init_output, List.nil_append, List.length_nil, Nat.cast_zero]
  · rfl

/-- The replay's body states along the choice word are `N`'s branch states. -/
private theorem xr_replay_state {N : FinNDTM Bool} (z s : List Bool) (h : Fin N.k → ℤ) (u : ℕ)
    (hu : u ≤ s.length) :
    (N.tm.replayTM.runFrom
      (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0) u).state =
      (N.tm.runWith (s.take u) (N.tm.initCfg z)).state := by
  obtain ⟨p, -, -, hrun⟩ := NDTM.replayTM_runFrom N.tm (xr_shift h (N.tm.initCfg z)) s u hu
  rw [hrun, NDTM.withChoiceTape_state, xr_runWith_shift]
  rfl

/-- **One replay, the `finish` exit.** If the branch along `s` first halts at `τ ≤ |s|`, and the
budget word `w` has value `|s|`, the replay phase reaches, within `5τ + 2|w| + 2` steps and with no
earlier exit, the exit `finish none` over `N`'s halted branch configuration, translated by `h`:
its input head and output, its work tapes and heads translated, the choice head at some `p ≤ τ`,
the counter rewritten to some word of the same width with its head at the origin, the output
captured with the capture head at its end, the depth tape untouched, and nothing emitted. -/
private theorem xr_replay_finish {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) (hval : Nat.ofDigits 2 (w.map Bool.toNat) = s.length) (τ : ℕ)
    (hτ : τ ≤ s.length) (hhalt : (N.tm.runWith (s.take τ) (N.tm.initCfg z)).state = none)
    (hlive : ∀ u < τ, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none) :
    ∃ T ≤ 5 * τ + 2 * w.length + 2, ∃ p ≤ τ, ∃ w' : List Bool, w'.length = w.length ∧
      (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) T =
        ⟨some (C.finish none), (N.tm.runWith (s.take τ) (N.tm.initCfg z)).inputPos,
          xr_tapes (xr_shift h (N.tm.runWith (s.take τ) (N.tm.initCfg z))).workTapes
            (FinTM.bufferTape s) (FinTM.bufferTape w')
            (FinTM.bufferTape (N.tm.runWith (s.take τ) (N.tm.initCfg z)).output)
            (FinTM.bufferTape wD),
          xr_heads (xr_shift h (N.tm.runWith (s.take τ) (N.tm.initCfg z))).workTapePos p 0
            ((N.tm.runWith (s.take τ) (N.tm.initCfg z)).output.length : ℤ) 0, []⟩ ∧
      ∀ u < T, ∀ r,
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.finish r) ∧
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.timeout r) := by
  have hq : (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0).state =
      some N.tm.q₀ := by
    rw [NDTM.withChoiceTape_state]
    show (N.tm.initCfg z).state = _
    rw [NDTM.initCfg_eq, Cfg.init_state]
  have hct : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      FinTM.bufferTape w (0 + p) = FinTM.bufferTape w p := fun p _ _ => by rw [zero_add]
  obtain ⟨T, hT, w', hw', hrun, hguard⟩ := C.spec_finish _ _ hq w (FinTM.bufferTape w) 0 hct τ
    (by rw [hval]; exact hτ) (by rw [xr_replay_state z s h τ hτ]; exact hhalt)
    (fun u hu => by rw [xr_replay_state z s h u (by omega)]; exact hlive u hu)
  obtain ⟨p, hp, -, hrep⟩ := NDTM.replayTM_runFrom N.tm (xr_shift h (N.tm.initCfg z)) s τ hτ
  rw [xr_runWith_shift] at hrep
  have hE : ∀ u, (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u =
      embedSilentCfg (xr_ι N.k) (xr_cap N.k) (fun _ => FinTM.bufferTape wD) (fun _ => 0) [] []
        (C.H.runFrom (clockCfg (some (C.inj N.tm.q₀))
          (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0)
          (FinTM.bufferTape w) 0) u) := fun u => by
    rw [xr_replayStart_eq, xr_replayTM, embedSilentTM_runFrom _ _ (xr_cap_not_mem N.k)]
  refine ⟨T, hT, p, hp, w', hw', ?_, fun u hu r => ?_⟩
  · rw [hE, hrun, hrep, xr_embed_eq, xr_wordPatch_buffer w w' hw', List.nil_append]
    rfl
  · rw [hE, embedSilentCfg_state]
    exact hguard u hu r

/-- **One replay, the `timeout` exit.** If the branch along `s` is still live after `|s|` steps
(and so at every earlier time), and the budget word `w` has value `|s|`, the replay phase reaches,
within `7|s| + 2|w| + 2` steps and with no earlier exit, the exit `timeout` carrying the branch's
live state, over `N`'s branch configuration translated by `h`, with the same bank layout as the
`finish` exit. -/
private theorem xr_replay_timeout {N : FinNDTM Bool} (C : xr_Clock N) (z s w wD : List Bool)
    (h : Fin N.k → ℤ) (hval : Nat.ofDigits 2 (w.map Bool.toNat) = s.length)
    (hlive : ∀ u ≤ s.length, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none) :
    ∃ T ≤ 5 * s.length + 2 * w.length + 2, ∃ p ≤ s.length, ∃ w' : List Bool,
      w'.length = w.length ∧
      (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) T =
        ⟨some (C.timeout (N.tm.runWith s (N.tm.initCfg z)).state),
          (N.tm.runWith s (N.tm.initCfg z)).inputPos,
          xr_tapes (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes
            (FinTM.bufferTape s) (FinTM.bufferTape w')
            (FinTM.bufferTape (N.tm.runWith s (N.tm.initCfg z)).output) (FinTM.bufferTape wD),
          xr_heads (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p 0
            ((N.tm.runWith s (N.tm.initCfg z)).output.length : ℤ) 0, []⟩ ∧
      ∀ u < T, ∀ r,
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.finish r) ∧
        ((xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u).state ≠ some (C.timeout r) := by
  have hq : (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0).state =
      some N.tm.q₀ := by
    rw [NDTM.withChoiceTape_state]
    show (N.tm.initCfg z).state = _
    rw [NDTM.initCfg_eq, Cfg.init_state]
  have hct : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) →
      FinTM.bufferTape w (0 + p) = FinTM.bufferTape w p := fun p _ _ => by rw [zero_add]
  obtain ⟨T, hT, w', hw', hrun, hguard⟩ := C.spec_timeout _ _ hq w (FinTM.bufferTape w) 0 hct
    (fun u hu => by rw [xr_replay_state z s h u (by omega)]; exact hlive u (by omega))
  rw [hval] at hT hrun
  obtain ⟨p, hp, -, hrep⟩ := NDTM.replayTM_runFrom N.tm (xr_shift h (N.tm.initCfg z)) s s.length
    le_rfl
  rw [xr_runWith_shift, List.take_length] at hrep
  have hE : ∀ u, (xr_replayTM C).runFrom (xr_replayStart C z s w wD h) u =
      embedSilentCfg (xr_ι N.k) (xr_cap N.k) (fun _ => FinTM.bufferTape wD) (fun _ => 0) [] []
        (C.H.runFrom (clockCfg (some (C.inj N.tm.q₀))
          (NDTM.withChoiceTape (xr_shift h (N.tm.initCfg z)) (FinTM.bufferTape s) 0)
          (FinTM.bufferTape w) 0) u) := fun u => by
    rw [xr_replayStart_eq, xr_replayTM, embedSilentTM_runFrom _ _ (xr_cap_not_mem N.k)]
  refine ⟨T, hT, p, hp, w', hw', ?_, fun u hu r => ?_⟩
  · rw [hE, hrun, hrep, xr_embed_eq, xr_wordPatch_buffer w w' hw', List.nil_append,
      NDTM.withChoiceTape_state]
    rfl
  · rw [hE, embedSilentCfg_state]
    exact hguard u hu r

/-! #### The host: its phases, its redirect table, and one phase's step

The exhaustive replay is `Turing.phaseHostTM` over the phases of one depth (copy the depth word
to the clock's counter; one replay; the capture test; the choice and input rewinds; the window
clear, six passes per work tape; the increment of the choice word) and of a depth change (extend
the choice word and the depth word, increment the depth word), with two flags in the phase index,
and the answer phases. The accept flag is raised when a replay of the current depth captures the
output exactly `[true]`, whether or not that branch has halted; the live flag, when a branch is
still live after the depth's steps. A depth change lowers both, so the accept flag is read only at
the first depth at which every branch has halted. -/

/-- **The first arrival at a stationary anchor, over a family of anchors.** If every state in `A`
is stationary and a run reaches `c'` in a state of `A` at time `T`, the first time the state is in
`A` is at most `T`, reaches `c'` too, and no earlier state is in `A`. -/
private theorem xr_firstArrival' {k : ℕ} {S : Type} {x : List Bool} (tm : MultiTapeTM k Bool S)
    (A : S → Prop)
    (hstat : ∀ d : Cfg k Bool S x, ∀ a, d.state = some a → A a → tm.step d = d)
    {c c' : Cfg k Bool S x} {T : ℕ} (h : tm.runFrom c T = c') {a : S} (hc' : c'.state = some a)
    (ha : A a) :
    ∃ T' ≤ T, tm.runFrom c T' = c' ∧
      ∀ u < T', ∀ a', (tm.runFrom c u).state = some a' → ¬ A a' := by
  classical
  have hT' : ∃ a', (tm.runFrom c T).state = some a' ∧ A a' := ⟨a, by rw [h]; exact hc', ha⟩
  have hex : ∃ u, ∃ a', (tm.runFrom c u).state = some a' ∧ A a' := ⟨T, hT'⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hT', ?_,
    fun u hu a' ha' hA => Nat.find_min hex hu ⟨a', ha', hA⟩⟩
  obtain ⟨a'', ha'', hA''⟩ := Nat.find_spec hex
  have hsplit : tm.runFrom c T = tm.runFrom (tm.runFrom c (Nat.find hex)) (T - Nat.find hex) := by
    rw [← MultiTapeTM.runFrom_add, Nat.add_sub_cancel' (Nat.find_min' hex hT')]
  rw [xr_runFrom_fixed tm _ (hstat _ a'' ha'' hA'')] at hsplit
  exact hsplit.symm.trans h

/-- Every `done` anchor of a leaf row whose table is stationary there is stationary. -/
private theorem xr_done_stationary {K : ℕ} {x : List Bool} (tm : MultiTapeTM K Bool xr_St)
    (htr : ∀ b inp w, tm.tr (.done b) inp w = xr_stay (.done b)) (d : Cfg K Bool xr_St x)
    (a : xr_St) (hd : d.state = some a) (ha : ∃ b, a = .done b) : tm.step d = d := by
  obtain ⟨b, rfl⟩ := ha
  exact xr_stay_step tm (.done b) (htr b) d hd

/-! ##### The banks are distinct -/

private theorem xr_work_val {k : ℕ} (j : Fin k) : (xr_work k j).val = j.val := by
  simp [xr_work]
private theorem xr_choice_val (k : ℕ) : (xr_choice k).val = k := by
  simp [xr_choice]
private theorem xr_ctr_val (k : ℕ) : (xr_ctr k).val = k + 1 := by
  simp [xr_ctr]
private theorem xr_cap_val (k : ℕ) : (xr_cap k).val = k + 2 := by
  simp [xr_cap]
private theorem xr_dep_val (k : ℕ) : (xr_dep k).val = k + 3 := by
  simp [xr_dep]

private theorem xr_work_ne_choice {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_choice k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_choice_val] at this; omega
private theorem xr_work_ne_ctr {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_ctr k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_ctr_val] at this; omega
private theorem xr_work_ne_cap {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_cap k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_cap_val] at this; omega
private theorem xr_work_ne_dep {k : ℕ} (j : Fin k) : xr_work k j ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_work_val, xr_dep_val] at this; omega
private theorem xr_choice_ne_ctr (k : ℕ) : xr_choice k ≠ xr_ctr k := by
  intro h; have := congrArg Fin.val h; rw [xr_choice_val, xr_ctr_val] at this; omega
private theorem xr_choice_ne_cap (k : ℕ) : xr_choice k ≠ xr_cap k := by
  intro h; have := congrArg Fin.val h; rw [xr_choice_val, xr_cap_val] at this; omega
private theorem xr_choice_ne_dep (k : ℕ) : xr_choice k ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_choice_val, xr_dep_val] at this; omega
private theorem xr_ctr_ne_cap (k : ℕ) : xr_ctr k ≠ xr_cap k := by
  intro h; have := congrArg Fin.val h; rw [xr_ctr_val, xr_cap_val] at this; omega
private theorem xr_ctr_ne_dep (k : ℕ) : xr_ctr k ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_ctr_val, xr_dep_val] at this; omega
private theorem xr_cap_ne_dep (k : ℕ) : xr_cap k ≠ xr_dep k := by
  intro h; have := congrArg Fin.val h; rw [xr_cap_val, xr_dep_val] at this; omega
private theorem xr_work_injective {k : ℕ} {j j' : Fin k} (h : xr_work k j = xr_work k j') :
    j = j' := by
  apply Fin.ext
  have := congrArg Fin.val h
  rwa [xr_work_val, xr_work_val] at this

/-- Two functions on `E`'s tape indices agree when they agree on every bank. -/
private theorem xr_bank_ext {k : ℕ} {α : Type} (F G : Fin (k + 2 + 2) → α)
    (hw : ∀ j, F (xr_work k j) = G (xr_work k j)) (hch : F (xr_choice k) = G (xr_choice k))
    (hctr : F (xr_ctr k) = G (xr_ctr k)) (hcap : F (xr_cap k) = G (xr_cap k))
    (hdep : F (xr_dep k) = G (xr_dep k)) : F = G := by
  funext j
  rcases xr_addCases_split j with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
    · exact hctr
    · rcases xr_lastCases_split i with rfl | ⟨i, rfl⟩
      · exact hch
      · exact hw i
  · rcases xr_fin2 i with rfl | rfl
    · exact hcap
    · exact hdep

/-! ##### Updating one bank -/

private theorem xr_tapes_upd_work {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp) (j : Fin k)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_work k j) X =
      xr_tapes (Function.update wk j X) ch ctr cp dp := by
  apply xr_bank_ext
  · intro j'
    by_cases hj : j' = j
    · subst hj; rw [Function.update_self, xr_tapes_work, Function.update_self]
    · rw [Function.update_of_ne (fun h => hj (xr_work_injective h)), xr_tapes_work, xr_tapes_work,
        Function.update_of_ne hj]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_choice j)), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_ctr j)), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_cap j)), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_dep j)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_choice {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_choice k) X = xr_tapes wk X ctr cp dp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_choice j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_self, xr_tapes_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_ctr k)), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_cap k)), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_dep k)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_ctr {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_ctr k) X = xr_tapes wk ch X cp dp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_ctr j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_of_ne (xr_choice_ne_ctr k), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_self, xr_tapes_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_ctr_ne_cap k)), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_ctr_ne_dep k)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_cap {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_cap k) X = xr_tapes wk ch ctr X dp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_cap j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_of_ne (xr_choice_ne_cap k), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_cap k), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_self, xr_tapes_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_cap_ne_dep k)), xr_tapes_dep, xr_tapes_dep]

private theorem xr_tapes_upd_dep {k : ℕ} (wk : Fin k → ℤ → Option Bool) (ch ctr cp dp)
    (X : ℤ → Option Bool) :
    Function.update (xr_tapes wk ch ctr cp dp) (xr_dep k) X = xr_tapes wk ch ctr cp X := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_dep j), xr_tapes_work, xr_tapes_work]
  · rw [Function.update_of_ne (xr_choice_ne_dep k), xr_tapes_choice, xr_tapes_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_dep k), xr_tapes_ctr, xr_tapes_ctr]
  · rw [Function.update_of_ne (xr_cap_ne_dep k), xr_tapes_cap, xr_tapes_cap]
  · rw [Function.update_self, xr_tapes_dep]

private theorem xr_heads_upd_work {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (j : Fin k)
    (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_work k j) X =
      xr_heads (Function.update hk j X) hch hctr hcp hdp := by
  apply xr_bank_ext
  · intro j'
    by_cases hj : j' = j
    · subst hj; rw [Function.update_self, xr_heads_work, Function.update_self]
    · rw [Function.update_of_ne (fun h => hj (xr_work_injective h)), xr_heads_work, xr_heads_work,
        Function.update_of_ne hj]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_choice j)), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_ctr j)), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_cap j)), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_work_ne_dep j)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_choice {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_choice k) X =
      xr_heads hk X hctr hcp hdp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_choice j), xr_heads_work, xr_heads_work]
  · rw [Function.update_self, xr_heads_choice]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_ctr k)), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_cap k)), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_choice_ne_dep k)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_cap {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_cap k) X = xr_heads hk hch hctr X hdp := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_cap j), xr_heads_work, xr_heads_work]
  · rw [Function.update_of_ne (xr_choice_ne_cap k), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_cap k), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_self, xr_heads_cap]
  · rw [Function.update_of_ne (Ne.symm (xr_cap_ne_dep k)), xr_heads_dep, xr_heads_dep]

private theorem xr_heads_upd_dep {k : ℕ} (hk : Fin k → ℤ) (hch hctr hcp hdp : ℤ) (X : ℤ) :
    Function.update (xr_heads hk hch hctr hcp hdp) (xr_dep k) X = xr_heads hk hch hctr hcp X := by
  apply xr_bank_ext
  · intro j; rw [Function.update_of_ne (xr_work_ne_dep j), xr_heads_work, xr_heads_work]
  · rw [Function.update_of_ne (xr_choice_ne_dep k), xr_heads_choice, xr_heads_choice]
  · rw [Function.update_of_ne (xr_ctr_ne_dep k), xr_heads_ctr, xr_heads_ctr]
  · rw [Function.update_of_ne (xr_cap_ne_dep k), xr_heads_cap, xr_heads_cap]
  · rw [Function.update_self, xr_heads_dep]

/-- **The catalog rows' result tape.** A row that rewrites the cells `[0, |w|)` of a bank holding
the word `w` at the origin with a same-width word `v` leaves that bank holding `v`. -/
private theorem xr_patch_eq {K : ℕ} (tp : Fin K → ℤ → Option Bool) (hd : Fin K → ℤ) (i : Fin K)
    (hi : hd i = 0) (w v w₀ : List Bool) (hv : v.length = w.length)
    (hw : tp i = FinTM.bufferTape w₀)
    (hlen : w₀.length ≤ w.length) :
    (fun j q => if j = i ∧ hd j ≤ q ∧ q < hd j + (w.length : ℤ) then FinTM.bufferTape v (q - hd j)
      else tp j q) = Function.update tp i (FinTM.bufferTape v) := by
  funext j q
  by_cases hj : j = i
  · subst hj
    rw [Function.update_self, hi, hw, sub_zero, zero_add]
    by_cases h : 0 ≤ q ∧ q < (w.length : ℤ)
    · rw [if_pos ⟨rfl, h⟩]
    · rw [if_neg (fun h' => h h'.2), (xr_bufferTape_eq_none_iff _ _).mpr (by omega),
        (xr_bufferTape_eq_none_iff _ _).mpr (by omega)]
  · rw [Function.update_of_ne hj, if_neg (fun h' => hj h'.1)]

/-! ##### The counter words: little-endian binary values -/

/-- The value of a binary word, little-endian. -/
private def xr_val (w : List Bool) : ℕ := Nat.ofDigits 2 (w.map Bool.toNat)

private theorem xr_val_nil : xr_val [] = 0 := by
  simp [xr_val]

private theorem xr_val_cons (b : Bool) (w : List Bool) :
    xr_val (b :: w) = b.toNat + 2 * xr_val w := by
  simp [xr_val, Nat.ofDigits_cons]

private theorem xr_val_lt (w : List Bool) : xr_val w < 2 ^ w.length := by
  have := Nat.ofDigits_lt_base_pow_length (b := 2) (l := w.map Bool.toNat) (by norm_num)
    (by intro x hx; obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; cases b <;> simp)
  simpa [xr_val] using this

private theorem xr_val_inj :
    ∀ {w w' : List Bool}, w.length = w'.length → xr_val w = xr_val w' → w = w'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | b :: w, b' :: w', h, hv => by
    rw [xr_val_cons, xr_val_cons] at hv
    have hb : b = b' := by
      cases b <;> cases b' <;> simp at hv ⊢ <;> omega
    subst hb
    have hw : xr_val w = xr_val w' := by omega
    rw [xr_val_inj (by simpa using h) hw]

private theorem xr_val_append_false (w : List Bool) : xr_val (w ++ [false]) = xr_val w := by
  simp [xr_val, Nat.ofDigits_append]

private theorem xr_val_replicate_false (n : ℕ) : xr_val (List.replicate n false) = 0 := by
  induction n with
  | zero => exact xr_val_nil
  | succ n ih => rw [List.replicate_succ, xr_val_cons, ih]; rfl

private theorem xr_val_replicate_true (n : ℕ) : xr_val (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rw [List.replicate_zero, xr_val_nil]; rfl
  | succ n ih => rw [List.replicate_succ, xr_val_cons, pow_succ]; simp only [Bool.toNat_true]; omega

/-- The increment adds one to the value. -/
private theorem xr_incFixed_val : ∀ {w v : List Bool}, incFixed w = some v → xr_val v = xr_val w + 1
  | [], _, h => by rw [incFixed_nil] at h; exact absurd h (by simp)
  | false :: w, v, h => by
    rw [incFixed_false_cons, Option.some.injEq] at h
    subst h
    rw [xr_val_cons, xr_val_cons]
    simp only [Bool.toNat_false, Bool.toNat_true]
    omega
  | true :: w, v, h => by
    rw [incFixed_true_cons] at h
    obtain ⟨v', hv', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [xr_val_cons, xr_val_cons, xr_incFixed_val hv']
    simp only [Bool.toNat_false, Bool.toNat_true]
    omega

/-- At the overflow the word is all `true`, so every same-length word has a value at most its. -/
private theorem xr_incFixed_none_max {w w' : List Bool} (h : incFixed w = none)
    (hlen : w'.length = w.length) : xr_val w' ≤ xr_val w := by
  have hrep := (incFixed_eq_none_iff_replicate w).mp h
  have h1 := xr_val_lt w'
  have h2 := xr_val_replicate_true w.length
  rw [hlen] at h1
  rw [hrep]
  omega

/-- A word not entirely `true` increments. -/
private theorem xr_incFixed_append_false (w : List Bool) :
    ∃ v, incFixed (w ++ [false]) = some v := by
  rcases h : incFixed (w ++ [false]) with _ | v
  · exfalso
    have := (incFixed_eq_none_iff_replicate _).mp h
    have hmem : false ∈ List.replicate (w ++ [false]).length true := by
      rw [← this]; simp
    simp at hmem
  · exact ⟨v, rfl⟩

/-! ##### The phase index, the phase machines and the redirect table -/

/-- The phases of the exhaustive replay. -/
private inductive xr_Ph (k : ℕ) where
  /-- copy the depth word onto the clock's counter -/
  | copy
  /-- the clocked replay -/
  | replay
  /-- the capture test, which also clears the captured output -/
  | test
  /-- rewind the choice head -/
  | crewind
  /-- rewind the input head -/
  | irewind
  /-- pass `n` of the window clear of work tape `j`: `n < 2` leftward, then rightward -/
  | pass (j : Fin k) (n : Fin 6)
  /-- increment the choice word -/
  | inc
  /-- extend the choice word by one `false` (a depth change) -/
  | extC
  /-- extend the depth word by one `false` (a depth change) -/
  | extD
  /-- increment the depth word (a depth change) -/
  | incD
  /-- the end: a stationary anchor the seam reads, the answer in the accept flag -/
  | halt
  deriving DecidableEq, Fintype

/-- The phase index: a phase with the accept flag (a replay of this depth captured the output
`[true]`) and the live flag (a branch is still live). -/
private abbrev xr_I (k : ℕ) := xr_Ph k × Bool × Bool

/-- Each phase's control. -/
private def xr_PhSt {N : FinNDTM Bool} (C : xr_Clock N) : xr_I N.k → Type
  | (.copy, _, _) => SweepPhase
  | (.replay, _, _) => C.Q
  | (.test, _, _) => xr_St
  | (.crewind, _, _) => xr_St
  | (.irewind, _, _) => xr_St
  | (.pass _ _, _, _) => xr_St
  | (.inc, _, _) => FlagPhase
  | (.extC, _, _) => xr_St
  | (.extD, _, _) => xr_St
  | (.incD, _, _) => FlagPhase
  | (.halt, _, _) => xr_St

private instance xr_PhSt_fintype {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i, Fintype (xr_PhSt C i)
  | (.copy, _, _) => inferInstanceAs (Fintype SweepPhase)
  | (.replay, _, _) => inferInstanceAs (Fintype C.Q)
  | (.test, _, _) => inferInstanceAs (Fintype xr_St)
  | (.crewind, _, _) => inferInstanceAs (Fintype xr_St)
  | (.irewind, _, _) => inferInstanceAs (Fintype xr_St)
  | (.pass _ _, _, _) => inferInstanceAs (Fintype xr_St)
  | (.inc, _, _) => inferInstanceAs (Fintype FlagPhase)
  | (.extC, _, _) => inferInstanceAs (Fintype xr_St)
  | (.extD, _, _) => inferInstanceAs (Fintype xr_St)
  | (.incD, _, _) => inferInstanceAs (Fintype FlagPhase)
  | (.halt, _, _) => inferInstanceAs (Fintype xr_St)

private instance xr_PhSt_decEq {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i, DecidableEq (xr_PhSt C i)
  | (.copy, _, _) => inferInstanceAs (DecidableEq SweepPhase)
  | (.replay, _, _) => inferInstanceAs (DecidableEq C.Q)
  | (.test, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.crewind, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.irewind, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.pass _ _, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.inc, _, _) => inferInstanceAs (DecidableEq FlagPhase)
  | (.extC, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.extD, _, _) => inferInstanceAs (DecidableEq xr_St)
  | (.incD, _, _) => inferInstanceAs (DecidableEq FlagPhase)
  | (.halt, _, _) => inferInstanceAs (DecidableEq xr_St)

/-- The direction of pass `n`: the first two passes move left, the last four right. -/
private def xr_dir (n : Fin 6) : SignType := if n.val < 2 then SignType.neg else SignType.pos

/-- The idle row: stationary everywhere (the `halt` phase, which the host never steps). -/
private def xr_idleTM (K : ℕ) : MultiTapeTM K Bool xr_St where
  q₀ := .start
  tr := fun q _ _ => xr_stay q

/-- The phase machines. -/
private def xr_M {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i : xr_I N.k, MultiTapeTM (N.k + 2 + 2) Bool (xr_PhSt C i)
  | (.copy, _, _) => copyTM (N.k + 2 + 2) (xr_dep N.k) (xr_ctr N.k)
  | (.replay, _, _) => xr_replayTM C
  | (.test, _, _) => xr_testTM (N.k + 2 + 2) (xr_cap N.k)
  | (.crewind, _, _) => xr_rewindTM (N.k + 2 + 2) (xr_choice N.k)
  | (.irewind, _, _) => xr_inRewindTM (N.k + 2 + 2)
  | (.pass j n, _, _) => xr_passTM (N.k + 2 + 2) (xr_work N.k j) (xr_dep N.k) (xr_dir n)
  | (.inc, _, _) => incrementTM (N.k + 2 + 2) (xr_choice N.k)
  | (.extC, _, _) => xr_extendTM (N.k + 2 + 2) (xr_choice N.k)
  | (.extD, _, _) => xr_extendTM (N.k + 2 + 2) (xr_dep N.k)
  | (.incD, _, _) => incrementTM (N.k + 2 + 2) (xr_dep N.k)
  | (.halt, _, _) => xr_idleTM (N.k + 2 + 2)

/-- The first phase of the window clear (the increment when `N` has no work tape). -/
private def xr_firstPass {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) : Σ i, xr_PhSt C i :=
  if h : 0 < N.k then ⟨(.pass ⟨0, h⟩ 0, a, l), xr_St.run⟩ else ⟨(.inc, a, l), FlagPhase.run⟩

/-- The phase after pass `n` of tape `j`: the next pass, the next tape, or the increment. -/
private def xr_afterPass {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (j : Fin N.k)
    (n : Fin 6) : Σ i, xr_PhSt C i :=
  if h : n.val + 1 < 6 then ⟨(.pass j ⟨n.val + 1, h⟩, a, l), xr_St.run⟩
  else if h' : j.val + 1 < N.k then ⟨(.pass ⟨j.val + 1, h'⟩ 0, a, l), xr_St.run⟩
  else ⟨(.inc, a, l), FlagPhase.run⟩

/-- The redirect of a leaf row's anchor `done b` at phase `i`, when the phase redirects on a
`done` state at all. -/
private def xr_redDone {N : FinNDTM Bool} (C : xr_Clock N) (i : xr_I N.k) (b : Bool) :
    Option (Σ i, xr_PhSt C i) :=
  match i with
  | (.test, a, l) => some ⟨(.crewind, a || b, l), xr_St.start⟩
  | (.crewind, a, l) => if b then some ⟨(.irewind, a, l), xr_St.start⟩ else none
  | (.irewind, a, l) => if b then some (xr_firstPass C a l) else none
  | (.pass j n, a, l) => if b then some (xr_afterPass C a l j n) else none
  | (.extC, a, l) => if b then some ⟨(.extD, a, l), xr_St.run⟩ else none
  | (.extD, a, l) => if b then some ⟨(.incD, a, l), FlagPhase.run⟩ else none
  | _ => none

open Classical in
/-- The redirect table. -/
private noncomputable def xr_red {N : FinNDTM Bool} (C : xr_Clock N) :
    ∀ i : xr_I N.k, xr_PhSt C i → Option (Σ i, xr_PhSt C i)
  | (.copy, a, l), s => if s = SweepPhase.done then some ⟨(.replay, a, l), C.inj N.tm.q₀⟩ else none
  | (.replay, a, l), q =>
    if ∃ r, q = C.finish r then some ⟨(.test, a, l), xr_St.start⟩
    else if ∃ r, q = C.timeout r then some ⟨(.test, a, true), xr_St.start⟩ else none
  | (.test, a, l), s => match s with | .done b => xr_redDone C (.test, a, l) b | _ => none
  | (.crewind, a, l), s => match s with | .done b => xr_redDone C (.crewind, a, l) b | _ => none
  | (.irewind, a, l), s => match s with | .done b => xr_redDone C (.irewind, a, l) b | _ => none
  | (.pass j n, a, l), s => match s with | .done b => xr_redDone C (.pass j n, a, l) b | _ => none
  | (.inc, a, l), s =>
    match s with
    | .done true => some ⟨(.copy, a, l), SweepPhase.sweep⟩
    | .done false =>
      some (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.halt, a, false), xr_St.start⟩)
    | _ => none
  | (.extC, a, l), s => match s with | .done b => xr_redDone C (.extC, a, l) b | _ => none
  | (.extD, a, l), s => match s with | .done b => xr_redDone C (.extD, a, l) b | _ => none
  | (.incD, a, l), s => match s with | .done _ => some ⟨(.copy, a, l), SweepPhase.sweep⟩ | _ => none
  | (.halt, a, l), _ => some ⟨(.halt, a, l), xr_St.start⟩

/-- **The host of the exhaustive replay**: the phase host over the phases above, starting at the
copy with both flags down. The machine `E` is the two-exit seam of this host onto the two
one-step answers. -/
private noncomputable def xr_host {N : FinNDTM Bool} (C : xr_Clock N) :
    MultiTapeTM (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) :=
  phaseHostTM (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)

/-- **One phase of the host.** If phase `i`, started at `s₀` over the tapes `tp` and heads `hd`,
reaches `c'` in `T` steps, `c'` is in a state `s'` that the table redirects to `q'`, and no earlier
state is redirected, then the host, started at `⟨i, s₀⟩` over the same tapes, reaches `c'`'s tapes
and heads in state `q'` in `T + 1` steps. -/
private theorem xr_phase_step {N : FinNDTM Bool} (C : xr_Clock N) {z : List Bool} (i : xr_I N.k)
    (s₀ : xr_PhSt C i) (ip : Fin (z.length + 2)) (tp : Fin (N.k + 2 + 2) → ℤ → Option Bool)
    (hd : Fin (N.k + 2 + 2) → ℤ) (T : ℕ) (c' : Cfg (N.k + 2 + 2) Bool (xr_PhSt C i) z)
    (h : (xr_M C i).runFrom ⟨some s₀, ip, tp, hd, []⟩ T = c') (s' : xr_PhSt C i)
    (hs' : c'.state = some s') (hout : c'.output = []) (q' : Σ i, xr_PhSt C i)
    (hred : xr_red C i s' = some q')
    (hguard : ∀ u < T, ∀ s, ((xr_M C i).runFrom ⟨some s₀, ip, tp, hd, []⟩ u).state = some s →
      xr_red C i s = none) :
    (xr_host C).runFrom ⟨some ⟨i, s₀⟩, ip, tp, hd, []⟩ (T + 1) =
      ⟨some q', c'.inputPos, c'.workTapes, c'.workTapePos, []⟩ := by
  have hstart : (⟨some ⟨i, s₀⟩, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) =
      (⟨some s₀, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (xr_PhSt C i) z).mapState
        (Sigma.mk i) :=
    (Cfg.mapState_eq_of_fields (⟨some s₀, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool (xr_PhSt C i) z)
      (Sigma.mk i) _ rfl rfl rfl rfl rfl).symm
  have hhost := (phaseHostTM_run (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C) i _
    c' T h s' hs' q' hred hguard).2
  rw [hstart]
  show (phaseHostTM (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)).runFrom _
    (T + 1) = _
  rw [hhost]
  exact Cfg.mapState_eq_of_fields _ _ _ (by rw [hs']; rfl) rfl rfl rfl hout

/-! #### One cycle: the phases of one replay, on the host

The configurations between phases, by banks, and each phase's effect on the host, from the
rows' run lemmas through `xr_phase_step`. -/

/-- `E` at the start of a cycle at depth `|s|`: the copy phase with the flags `a` and `l`, the
depth word `wL` on the depth tape, the choice word `s`, some word `u` on the counter, the capture
tape blank, `N`'s tapes blank with their heads at `h`, the input head at `1`. -/
private def xr_cycle {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s u : List Bool) (h : Fin N.k → ℤ) : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z :=
  ⟨some ⟨(.copy, a, l), SweepPhase.sweep⟩, 1,
    xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
      (FinTM.bufferTape wL),
    xr_heads h 0 0 0 0, []⟩

/-- `E` at the end of a depth, after the choice word's overflow: the deepening when some branch
was live, else the answer; the choice tape holds the all-`false` word again. -/
private def xr_depthEnd {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (L : ℕ) (wL u : List Bool) (h : Fin N.k → ℤ) : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z :=
  ⟨some (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.halt, a, false), xr_St.start⟩), 1,
    xr_tapes (fun _ _ => none) (FinTM.bufferTape (List.replicate L false)) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL),
    xr_heads h 0 0 0 0, []⟩

/-- A branch of length `|s|` moves the input head at most `|s|` cells from its start at `1`
(through the replay machine and `Turing.MultiTapeTM.timed_input_bound`). -/
private theorem xr_branch_inputPos_le {N : FinNDTM Bool} (z s : List Bool) :
    (N.tm.runWith s (N.tm.initCfg z)).inputPos.val ≤ 1 + s.length := by
  obtain ⟨p, -, -, hrun⟩ := NDTM.replayTM_runFrom N.tm (N.tm.initCfg z) s s.length le_rfl
  have h := MultiTapeTM.timed_input_bound (tm := N.tm.replayTM)
    (NDTM.withChoiceTape (N.tm.initCfg z) (FinTM.bufferTape s) 0) s.length
  rw [hrun, NDTM.withChoiceTape_inputPos, NDTM.withChoiceTape_inputPos, List.take_length,
    NDTM.initCfg_eq, Cfg.init_inputPos] at h
  simpa [NDTM.initCfg_eq] using h

/-! ##### The redirect table, read -/

private theorem xr_red_copy_done {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) :
    xr_red C (.copy, a, l) SweepPhase.done = some ⟨(.replay, a, l), C.inj N.tm.q₀⟩ := by
  simp [xr_red]

private theorem xr_red_copy_none {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool)
    (s : SweepPhase) (hs : s ≠ SweepPhase.done) : xr_red C (.copy, a, l) s = none := by
  simp [xr_red, hs]

private theorem xr_red_replay_finish {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool)
    (r : Option N.State) :
    xr_red C (.replay, a, l) (C.finish r) = some ⟨(.test, a, l), xr_St.start⟩ := by
  show (if ∃ r', C.finish r = C.finish r' then _ else _) = _
  rw [if_pos ⟨r, rfl⟩]

private theorem xr_red_replay_timeout {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool)
    (r : Option N.State) :
    xr_red C (.replay, a, l) (C.timeout r) = some ⟨(.test, a, true), xr_St.start⟩ := by
  show (if ∃ r', C.timeout r = C.finish r' then _
    else if ∃ r', C.timeout r = C.timeout r' then _ else _) = _
  rw [if_neg (fun ⟨r', hr'⟩ => C.finish_ne_timeout r' r hr'.symm), if_pos ⟨r, rfl⟩]

private theorem xr_red_replay_none {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (q : C.Q)
    (hq : ∀ r, q ≠ C.finish r ∧ q ≠ C.timeout r) : xr_red C (.replay, a, l) q = none := by
  show (if ∃ r', q = C.finish r' then _ else if ∃ r', q = C.timeout r' then _ else _) = _
  rw [if_neg (fun ⟨r', hr'⟩ => (hq r').1 hr'), if_neg (fun ⟨r', hr'⟩ => (hq r').2 hr')]

/-- The phases run by a leaf row redirect only at a `done` anchor. -/
private theorem xr_red_leaf_none {N : FinNDTM Bool} (C : xr_Clock N) (i : xr_I N.k)
    (hi : (∃ a l, i = (.test, a, l)) ∨ (∃ a l, i = (.crewind, a, l)) ∨
      (∃ a l, i = (.irewind, a, l)) ∨ (∃ j n a l, i = (.pass j n, a, l)) ∨
      (∃ a l, i = (.extC, a, l)) ∨ (∃ a l, i = (.extD, a, l)))
    (s : xr_St) (hs : ¬ ∃ b, s = .done b) :
    ∀ (e : xr_PhSt C i = xr_St), xr_red C i (e ▸ s) = none := by
  intro e
  rcases hi with h | h | h | h | h | h
  all_goals first
    | (obtain ⟨a, l, rfl⟩ := h; cases s <;> first | rfl | exact absurd ⟨_, rfl⟩ hs)
    | (obtain ⟨j, n, a, l, rfl⟩ := h; cases s <;> first | rfl | exact absurd ⟨_, rfl⟩ hs)

/-! ##### The copy phase -/

/-- **The copy phase on the host.** From the start of a cycle, `2|wL| + 3` steps copy the depth
word onto the counter and dispatch to the replay. -/
private theorem xr_copy_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s u : List Bool) (h : Fin N.k → ℤ) (hu : u.length ≤ wL.length) :
    (xr_host C).runFrom (xr_cycle C z a l wL s u h) (2 * wL.length + 3) =
      ⟨some ⟨(.replay, a, l), C.inj N.tm.q₀⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape wL) (FinTM.bufferTape [])
          (FinTM.bufferTape wL),
        xr_heads h 0 0 0 0, []⟩ := by
  obtain ⟨hcfg, hguard, -⟩ := copyTM_run_ofCfg (xr_dep N.k) (xr_ctr N.k) (xr_ctr_ne_dep N.k).symm wL
    (⟨some SweepPhase.sweep, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool SweepPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_dep, xr_heads_dep, zero_add])
  rw [xr_cycle, xr_phase_step C (.copy, a, l) SweepPhase.sweep 1 _ _ (2 * wL.length + 2) _ hcfg
    SweepPhase.done rfl rfl _ (xr_red_copy_done C a l)
    (fun t ht s hs => by
      cases s with
      | done => exact absurd hs (hguard t ht)
      | sweep => exact xr_red_copy_none C a l _ (by simp)
      | rewind => exact xr_red_copy_none C a l _ (by simp))]
  dsimp only
  rw [xr_patch_eq _ _ (xr_ctr N.k) (xr_heads_ctr _ _ _ _ _) wL wL u rfl (xr_tapes_ctr _ _ _ _ _) hu,
    xr_tapes_upd_ctr]

/-! ##### The replay phase -/

/-- **The replay phase on the host.** From the copy's end, the clocked replay of the choice word
`s` runs, within `5|s| + 2|wL| + 3` steps, to the capture test, raising the live flag exactly when
the branch along `s` is live after `|s|` steps; the tapes hold the branch's configuration,
translated by `h`, with the output captured. -/
private theorem xr_replay_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s : List Bool) (h : Fin N.k → ℤ) (hval : xr_val wL = s.length) :
    ∃ T ≤ 5 * s.length + 2 * wL.length + 3, ∃ p ≤ s.length, ∃ w' : List Bool,
      w'.length = wL.length ∧
      (xr_host C).runFrom ⟨some ⟨(.replay, a, l), C.inj N.tm.q₀⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape wL) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ T =
      ⟨some ⟨(.test, a, l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome), xr_St.start⟩,
        (N.tm.runWith s (N.tm.initCfg z)).inputPos,
        xr_tapes (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes (FinTM.bufferTape s)
          (FinTM.bufferTape w') (FinTM.bufferTape (N.tm.runWith s (N.tm.initCfg z)).output)
          (FinTM.bufferTape wL),
        xr_heads (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p 0
          ((N.tm.runWith s (N.tm.initCfg z)).output.length : ℤ) 0, []⟩ := by
  classical
  by_cases hb : (N.tm.runWith s (N.tm.initCfg z)).state = none
  · -- the branch halts: the `finish` exit at the first halting time
    have hex : ∃ u, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state = none :=
      ⟨s.length, by rw [List.take_length]; exact hb⟩
    set τ := Nat.find hex with hτdef
    have hτ : τ ≤ s.length := Nat.find_min' hex (by rw [List.take_length]; exact hb)
    have hhalt : (N.tm.runWith (s.take τ) (N.tm.initCfg z)).state = none := Nat.find_spec hex
    have hlive : ∀ u < τ, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none :=
      fun u hu => Nat.find_min hex hu
    have hbτ : N.tm.runWith s (N.tm.initCfg z) = N.tm.runWith (s.take τ) (N.tm.initCfg z) := by
      conv_lhs => rw [← List.take_append_drop τ s]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
    obtain ⟨T, hT, p, hp, w', hw', hrun, hguard⟩ :=
      xr_replay_finish C z s wL wL h (by rw [← hval]; rfl) τ hτ hhalt hlive
    refine ⟨T + 1, by omega, p, hp.trans hτ, w', hw', ?_⟩
    rw [xr_phase_step C (.replay, a, l) (C.inj N.tm.q₀) 1 _ _ T _ hrun (C.finish none) rfl rfl _
      (xr_red_replay_finish C a l none)
      (fun u hu q hq => xr_red_replay_none C a l q (fun r =>
        ⟨fun h => (hguard u hu r).1 (by rw [h] at hq; exact hq),
          fun h => (hguard u hu r).2 (by rw [h] at hq; exact hq)⟩))]
    rw [hbτ, hhalt, Option.isSome_none, Bool.or_false]
  · -- the branch is live: the `timeout` exit
    have hlive : ∀ u ≤ s.length, (N.tm.runWith (s.take u) (N.tm.initCfg z)).state ≠ none := by
      intro u hu hhalt
      apply hb
      conv_lhs => rw [← List.take_append_drop u s]
      rw [NDTM.runWith_append, NDTM.runWith_of_halt _ hhalt]
      exact hhalt
    obtain ⟨T, hT, p, hp, w', hw', hrun, hguard⟩ :=
      xr_replay_timeout C z s wL wL h (by rw [← hval]; rfl) hlive
    refine ⟨T + 1, by omega, p, hp, w', hw', ?_⟩
    rw [xr_phase_step C (.replay, a, l) (C.inj N.tm.q₀) 1 _ _ T _ hrun _ rfl rfl _
      (xr_red_replay_timeout C a l _)
      (fun u hu q hq => xr_red_replay_none C a l q (fun r =>
        ⟨fun h => (hguard u hu r).1 (by rw [h] at hq; exact hq),
          fun h => (hguard u hu r).2 (by rw [h] at hq; exact hq)⟩))]
    rw [Option.isSome_iff_ne_none.mpr hb, Bool.or_true]

/-! ##### The capture test, the choice rewind, the input rewind -/

/-- **The capture test on the host.** With the output `out` captured, within `|out| + 3` steps the
host clears it, returns the capture head, raises the accept flag exactly when `out = [true]`, and
dispatches to the choice rewind. -/
private theorem xr_test_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr dp : ℤ → Option Bool)
    (hk : Fin N.k → ℤ) (hch hctr hdp : ℤ) (out : List Bool) :
    ∃ T ≤ out.length + 3,
      (xr_host C).runFrom ⟨some ⟨(.test, a, l), xr_St.start⟩, ip,
        xr_tapes wk ch ctr (FinTM.bufferTape out) dp, xr_heads hk hch hctr (out.length : ℤ) hdp, []⟩
        T =
      ⟨some ⟨(.crewind, a || decide (out = [true]), l), xr_St.start⟩, ip,
        xr_tapes wk ch ctr (FinTM.bufferTape []) dp, xr_heads hk hch hctr 0 hdp, []⟩ := by
  have hrun := xr_testTM_run (xr_cap N.k) out
    (⟨some xr_St.start, ip, xr_tapes wk ch ctr (FinTM.bufferTape out) dp,
      xr_heads hk hch hctr (out.length : ℤ) hdp, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
    (xr_tapes_cap _ _ _ _ _) (xr_heads_cap _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_testTM (N.k + 2 + 2) (xr_cap N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.test, a, l) xr_St.start ip _ _ T' _ hrun' _ rfl rfl
    ⟨(.crewind, a || decide (out = [true]), l), xr_St.start⟩ rfl
    (fun u hu s hs =>
      xr_red_leaf_none C (.test, a, l) (Or.inl ⟨a, l, rfl⟩) s (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_tapes_upd_cap, xr_heads_upd_cap, FinTM.bufferTape_nil]

/-- **The choice rewind on the host.** With the choice head at `p ≤ |s|`, within `p + 3` steps the
host returns it to the origin and dispatches to the input rewind. -/
private theorem xr_crewind_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (s : List Bool)
    (ctr cp dp : ℤ → Option Bool) (hk : Fin N.k → ℤ) (p : ℕ) (hp : p ≤ s.length)
    (hctr hcp hdp : ℤ) :
    ∃ T ≤ p + 3,
      (xr_host C).runFrom ⟨some ⟨(.crewind, a, l), xr_St.start⟩, ip,
        xr_tapes wk (FinTM.bufferTape s) ctr cp dp, xr_heads hk (p : ℤ) hctr hcp hdp, []⟩ T =
      ⟨some ⟨(.irewind, a, l), xr_St.start⟩, ip, xr_tapes wk (FinTM.bufferTape s) ctr cp dp,
        xr_heads hk 0 hctr hcp hdp, []⟩ := by
  have hrun := xr_rewindTM_run (xr_choice N.k) s p hp
    (⟨some xr_St.start, ip, xr_tapes wk (FinTM.bufferTape s) ctr cp dp,
      xr_heads hk (p : ℤ) hctr hcp hdp, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
    (xr_tapes_choice _ _ _ _ _) (xr_heads_choice _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_rewindTM (N.k + 2 + 2) (xr_choice N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.crewind, a, l) xr_St.start ip _ _ T' _ hrun' _ rfl rfl
    ⟨(.irewind, a, l), xr_St.start⟩ rfl
    (fun u hu s hs => xr_red_leaf_none C (.crewind, a, l) (Or.inr (Or.inl ⟨a, l, rfl⟩)) s
      (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_heads_upd_choice]

/-- **The input rewind on the host.** Within `inputPos + 3` steps the host returns the input head
to `1` and dispatches to the window clear (or to the increment when `N` has no work tape). -/
private theorem xr_irewind_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (tp : Fin (N.k + 2 + 2) → ℤ → Option Bool)
    (hd : Fin (N.k + 2 + 2) → ℤ) :
    ∃ T ≤ ip.val + 3,
      (xr_host C).runFrom ⟨some ⟨(.irewind, a, l), xr_St.start⟩, ip, tp, hd, []⟩ T =
        ⟨some (xr_firstPass C a l), 1, tp, hd, []⟩ := by
  obtain ⟨T₀, hT₀, hrun₀⟩ := FinTM.timed_rewind (xr_inRewindTM (N.k + 2 + 2)) .start .run
    (some (.done true)) (fun inp work => rfl) (fun inp work => by cases inp <;> rfl)
    (⟨some xr_St.start, ip, tp, hd, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
  have hT₀' : T₀ ≤ ip.val + 2 := hT₀
  obtain ⟨T', hT', hrun, hguard⟩ := xr_firstArrival' (xr_inRewindTM (N.k + 2 + 2))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun₀ rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.irewind, a, l) xr_St.start ip tp hd T' _ hrun (.done true) rfl rfl
    (xr_firstPass C a l) rfl
    (fun u hu s hs => xr_red_leaf_none C (.irewind, a, l) (Or.inr (Or.inr (Or.inl ⟨a, l, rfl⟩))) s
      (hguard u hu s hs) rfl)]

/-! ##### The increment of the choice word -/

/-- **The increment on the host, a successor.** When `incFixed s = some s'`, within `2|s| + 3`
steps the host writes `s'` on the choice tape and dispatches to the next cycle. -/
private theorem xr_inc_host_succ {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s s' u : List Bool) (hs' : incFixed s = some s') (hk : Fin N.k → ℤ) :
    ∃ T ≤ 2 * s.length + 3,
      (xr_host C).runFrom ⟨some ⟨(.inc, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ T = xr_cycle C z a l wL s' u hk := by
  obtain ⟨hcfg, hguard, -⟩ := incrementTM_run_succ_ofCfg (xr_choice N.k) s s' hs'
    (⟨some FlagPhase.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool FlagPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_choice, xr_heads_choice, zero_add])
  refine ⟨2 * (s.takeWhile id).length + 2 + 1, by
    have := (List.takeWhile_sublist (l := s) id).length_le; omega, ?_⟩
  rw [xr_phase_step C (.inc, a, l) FlagPhase.run 1 _ _ _ _ hcfg (FlagPhase.done true) rfl rfl
    ⟨(.copy, a, l), SweepPhase.sweep⟩ rfl
    (fun t ht s hs => by
      cases s with
      | done b => exact absurd hs (hguard t ht b)
      | run => rfl
      | rewind b => rfl)]
  dsimp only
  rw [xr_patch_eq _ _ (xr_choice N.k) (xr_heads_choice _ _ _ _ _) s s' s (incFixed_length hs')
    (xr_tapes_choice _ _ _ _ _) le_rfl, xr_tapes_upd_choice]
  rfl

/-- **The increment on the host, the overflow.** When `incFixed s = none`, `2|s| + 3` steps leave
the all-`false` word on the choice tape and dispatch to the depth's end. -/
private theorem xr_inc_host_overflow {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool)
    (a l : Bool) (wL s u : List Bool) (hs : incFixed s = none) (hk : Fin N.k → ℤ) :
    (xr_host C).runFrom ⟨some ⟨(.inc, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ (2 * s.length + 3) =
      xr_depthEnd C z a l s.length wL u hk := by
  obtain ⟨hcfg, hguard, -⟩ := incrementTM_run_overflow_ofCfg (xr_choice N.k) s hs
    (⟨some FlagPhase.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads hk 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool FlagPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_choice, xr_heads_choice, zero_add])
  rw [show 2 * s.length + 3 = 2 * s.length + 2 + 1 from rfl,
    xr_phase_step C (.inc, a, l) FlagPhase.run 1 _ _ _ _ hcfg (FlagPhase.done false) rfl rfl
    (if l then ⟨(.extC, false, false), xr_St.run⟩ else ⟨(.halt, a, false), xr_St.start⟩) rfl
    (fun t ht s hs => by
      cases s with
      | done b => exact absurd hs (hguard t ht b)
      | run => rfl
      | rewind b => rfl)]
  dsimp only
  rw [xr_patch_eq _ _ (xr_choice N.k) (xr_heads_choice _ _ _ _ _) s
    (List.replicate s.length false) s List.length_replicate (xr_tapes_choice _ _ _ _ _) le_rfl,
    xr_tapes_upd_choice]
  rfl

/-! ##### The window clear on the host -/

/-- Content within radius `R` of the cell `a`. -/
private def xr_Win (f : ℤ → Option Bool) (a R : ℤ) : Prop :=
  ∀ p, f p ≠ none → a - R ≤ p ∧ p ≤ a + R

/-- Blank on `[lo, hi]`. -/
private def xr_Blank (f : ℤ → Option Bool) (lo hi : ℤ) : Prop :=
  ∀ p, lo ≤ p → p ≤ hi → f p = none

private theorem xr_dir_cast (n : Fin 6) :
    ((xr_dir n : SignType) : ℤ) = if n.val < 2 then -1 else 1 := by
  unfold xr_dir
  split_ifs <;> rfl

/-- The phase at which the window clear of tape `m` starts (the increment when `m = N.k`). -/
private def xr_passStart {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (m : ℕ) :
    Σ i, xr_PhSt C i :=
  if h : m < N.k then ⟨(.pass ⟨m, h⟩ 0, a, l), xr_St.run⟩ else ⟨(.inc, a, l), FlagPhase.run⟩

private theorem xr_firstPass_eq {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) :
    xr_firstPass C a l = xr_passStart C a l 0 := rfl

private theorem xr_afterPass_last {N : FinNDTM Bool} (C : xr_Clock N) (a l : Bool) (j : Fin N.k) :
    xr_afterPass C a l j ⟨5, by omega⟩ = xr_passStart C a l (j.val + 1) := by
  unfold xr_afterPass xr_passStart
  rw [dif_neg (by decide)]

/-- **One pass on the host.** From the start of pass `n` of tape `j`, within `2|wL| + 3` steps head
`j` moves `|wL|` cells along the pass's direction, the cells between its start and its end are
blanked, the ruler head returns, and the host dispatches to the next pass. -/
private theorem xr_pass_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k) (n : Fin 6) :
    ∃ T ≤ 2 * wL.length + 3, ∃ f : ℤ → Option Bool,
      (xr_host C).runFrom ⟨some ⟨(.pass j n, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_afterPass C a l j n), ip, xr_tapes (Function.update wk j f) ch ctr cp
        (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j + wL.length * (if n.val < 2 then -1 else 1))) hch hctr
          hcp 0, []⟩ ∧
      (∀ p : ℤ, (∃ i : ℕ, i ≤ wL.length ∧ p = hk j + i * (if n.val < 2 then -1 else 1)) →
        f p = none) ∧
      (∀ p, f p = none ∨ f p = wk j p) := by
  obtain ⟨f, hrun, hblank, hkeep⟩ := xr_passTM_run (xr_work N.k j) (xr_dep N.k) (xr_work_ne_dep j)
    (xr_dir n) wL
    (⟨some xr_St.run, ip, xr_tapes wk ch ctr cp (FinTM.bufferTape wL),
      xr_heads hk hch hctr hcp 0, []⟩ : Cfg (N.k + 2 + 2) Bool xr_St z) rfl
    (xr_tapes_dep _ _ _ _ _) (xr_heads_dep _ _ _ _ _)
  simp only [xr_heads_work, xr_tapes_work, xr_dir_cast] at hrun hblank hkeep
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_passTM (N.k + 2 + 2) (xr_work N.k j)
    (xr_dep N.k) (xr_dir n)) (fun s => ∃ b, s = .done b)
    (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, f, ?_, hblank, ?_⟩
  · rw [xr_phase_step C (.pass j n, a, l) xr_St.run ip _ _ T' _ hrun' _ rfl rfl
      (xr_afterPass C a l j n) rfl
      (fun u hu s hs => xr_red_leaf_none C (.pass j n, a, l)
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨j, n, a, l, rfl⟩)))) s (hguard u hu s hs) rfl)]
    dsimp only
    rw [xr_tapes_upd_work, xr_heads_upd_work]
  · intro p
    by_cases h : ∃ i : ℕ, i ≤ wL.length ∧ p = hk j + i * (if n.val < 2 then -1 else 1)
    · exact Or.inl (hblank p h)
    · exact Or.inr (hkeep p (fun i hi hp => h ⟨i, hi, hp⟩))

/-- A leftward pass: head `j` moves `|wL|` cells left and `[hk j - |wL|, hk j]` is blanked. -/
private theorem xr_pass_left {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k) (n : Fin 6)
    (hn : n.val < 2) :
    ∃ T ≤ 2 * wL.length + 3, ∃ f : ℤ → Option Bool,
      (xr_host C).runFrom ⟨some ⟨(.pass j n, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_afterPass C a l j n), ip, xr_tapes (Function.update wk j f) ch ctr cp
        (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j - wL.length)) hch hctr hcp 0, []⟩ ∧
      xr_Blank f (hk j - wL.length) (hk j) ∧ (∀ p, f p = none ∨ f p = wk j p) := by
  obtain ⟨T, hT, f, hrun, hbl, hsub⟩ := xr_pass_host C z a l ip wk ch ctr cp wL hk hch hctr hcp j n
  have he : hk j + (wL.length : ℤ) * (-1) = hk j - wL.length := by ring
  rw [if_pos hn, he] at hrun
  refine ⟨T, hT, f, hrun, fun p hlo hhi => hbl p ⟨(hk j - p).toNat, by omega, ?_⟩, hsub⟩
  rw [if_pos hn]
  omega

/-- A rightward pass: head `j` moves `|wL|` cells right and `[hk j, hk j + |wL|]` is blanked. -/
private theorem xr_pass_right {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k) (n : Fin 6)
    (hn : ¬ n.val < 2) :
    ∃ T ≤ 2 * wL.length + 3, ∃ f : ℤ → Option Bool,
      (xr_host C).runFrom ⟨some ⟨(.pass j n, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_afterPass C a l j n), ip, xr_tapes (Function.update wk j f) ch ctr cp
        (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j + wL.length)) hch hctr hcp 0, []⟩ ∧
      xr_Blank f (hk j) (hk j + wL.length) ∧ (∀ p, f p = none ∨ f p = wk j p) := by
  obtain ⟨T, hT, f, hrun, hbl, hsub⟩ := xr_pass_host C z a l ip wk ch ctr cp wL hk hch hctr hcp j n
  have he : hk j + (wL.length : ℤ) * 1 = hk j + wL.length := by ring
  rw [if_neg hn, he] at hrun
  refine ⟨T, hT, f, hrun, fun p hlo hhi => hbl p ⟨(p - hk j).toNat, by omega, ?_⟩, hsub⟩
  rw [if_neg hn]
  omega

/-- Blank cells stay blank under a pass. -/
private theorem xr_Blank_mono {f g : ℤ → Option Bool} (h : ∀ p, g p = none ∨ g p = f p) {lo hi : ℤ}
    (hf : xr_Blank f lo hi) : xr_Blank g lo hi := by
  intro p hlo hhi
  rcases h p with h' | h'
  · exact h'
  · rw [h', hf p hlo hhi]

/-- A blank cell stays blank under a pass. -/
private theorem xr_none_mono {f g : ℤ → Option Bool} (h : ∀ p, g p = none ∨ g p = f p) {p : ℤ}
    (hf : f p = none) : g p = none := by
  rcases h p with h' | h'
  · exact h'
  · rw [h', hf]

/-- **The window clear of one tape on the host.** From the start of pass `0` of tape `j`, whose
content lies within radius `2|wL|` of its head, within `6(2|wL| + 3)` steps the six passes blank
the tape and move its head `2|wL|` cells right; the host dispatches to the next tape (or the
increment).

**Proof sketch.** Six passes of the ruler word `wL` over tape `j` (`xr_pass_left` twice, then
`xr_pass_right` four times), each blanking the `|wL| + 1` cells it visits: the head goes
`2|wL|` cells left, then `4|wL|` right, ending `2|wL|` right of its start. The visited cells
cover `[pos − 2|wL|, pos + 2|wL|]`, which contains the tape's content (`xr_Win`), and a blank
cell stays blank under the later passes (`xr_Blank_mono`, `xr_none_mono`), so the tape ends
blank. Each pass with its dispatch costs at most `2|wL| + 3` steps. -/
private theorem xr_clearTape_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (wk : Fin N.k → ℤ → Option Bool) (ch ctr cp : ℤ → Option Bool)
    (wL : List Bool) (hk : Fin N.k → ℤ) (hch hctr hcp : ℤ) (j : Fin N.k)
    (hwin : xr_Win (wk j) (hk j) (2 * wL.length)) :
    ∃ T ≤ 6 * (2 * wL.length + 3),
      (xr_host C).runFrom ⟨some ⟨(.pass j ⟨0, by omega⟩, a, l), xr_St.run⟩, ip,
        xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
      ⟨some (xr_passStart C a l (j.val + 1)), ip,
        xr_tapes (Function.update wk j (fun _ => none)) ch ctr cp (FinTM.bufferTape wL),
        xr_heads (Function.update hk j (hk j + 2 * wL.length)) hch hctr hcp 0, []⟩ := by
  have e0 : xr_afterPass C a l j ⟨0, by omega⟩ =
    ⟨(.pass j ⟨1, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e1 : xr_afterPass C a l j ⟨1, by omega⟩ =
    ⟨(.pass j ⟨2, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e2 : xr_afterPass C a l j ⟨2, by omega⟩ =
    ⟨(.pass j ⟨3, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e3 : xr_afterPass C a l j ⟨3, by omega⟩ =
    ⟨(.pass j ⟨4, by omega⟩, a, l), xr_St.run⟩ := rfl
  have e4 : xr_afterPass C a l j ⟨4, by omega⟩ =
    ⟨(.pass j ⟨5, by omega⟩, a, l), xr_St.run⟩ := rfl
  obtain ⟨T₀, hT₀, f₀, hrun₀, hbl₀, hsub₀⟩ :=
    xr_pass_left C z a l ip wk ch ctr cp wL hk hch hctr hcp j ⟨0, by omega⟩
      (by show (0 : ℕ) < 2; omega)
  rw [e0] at hrun₀
  obtain ⟨T₁, hT₁, f₁, hrun₁, hbl₁, hsub₁⟩ :=
    xr_pass_left C z a l ip (Function.update wk j f₀) ch ctr cp wL
      (Function.update hk j (hk j - wL.length)) hch hctr hcp j ⟨1, by omega⟩
      (by show (1 : ℕ) < 2; omega)
  rw [e1, Function.update_idem, Function.update_self, Function.update_idem] at hrun₁
  rw [Function.update_self] at hbl₁ hsub₁
  obtain ⟨T₂, hT₂, f₂, hrun₂, hbl₂, hsub₂⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₁) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length)) hch hctr hcp j ⟨2, by omega⟩
      (by show ¬ ((2 : ℕ) < 2); omega)
  rw [e2, Function.update_idem, Function.update_self, Function.update_idem] at hrun₂
  rw [Function.update_self] at hbl₂ hsub₂
  obtain ⟨T₃, hT₃, f₃, hrun₃, hbl₃, hsub₃⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₂) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length + wL.length)) hch hctr hcp j
      ⟨3, by omega⟩ (by show ¬ ((3 : ℕ) < 2); omega)
  rw [e3, Function.update_idem, Function.update_self, Function.update_idem] at hrun₃
  rw [Function.update_self] at hbl₃ hsub₃
  obtain ⟨T₄, hT₄, f₄, hrun₄, hbl₄, hsub₄⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₃) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length + wL.length + wL.length)) hch hctr hcp j
      ⟨4, by omega⟩ (by show ¬ ((4 : ℕ) < 2); omega)
  rw [e4, Function.update_idem, Function.update_self, Function.update_idem] at hrun₄
  rw [Function.update_self] at hbl₄ hsub₄
  obtain ⟨T₅, hT₅, f₅, hrun₅, hbl₅, hsub₅⟩ :=
    xr_pass_right C z a l ip (Function.update wk j f₄) ch ctr cp wL
      (Function.update hk j (hk j - wL.length - wL.length + wL.length + wL.length + wL.length))
      hch hctr hcp j ⟨5, by omega⟩ (by show ¬ ((5 : ℕ) < 2); omega)
  rw [xr_afterPass_last, Function.update_idem, Function.update_self, Function.update_idem]
    at hrun₅
  rw [Function.update_self] at hbl₅ hsub₅
  have hf : f₅ = fun _ => none := by
    funext p
    by_cases hin : hk j - 2 * wL.length ≤ p ∧ p ≤ hk j + 2 * wL.length
    · rcases le_or_gt p (hk j - wL.length) with h1 | h1
      · exact xr_Blank_mono hsub₅ (xr_Blank_mono hsub₄ (xr_Blank_mono hsub₃ (xr_Blank_mono hsub₂
          hbl₁))) p (by omega) (by omega)
      · rcases le_or_gt p (hk j) with h2 | h2
        · exact xr_Blank_mono hsub₅ (xr_Blank_mono hsub₄ (xr_Blank_mono hsub₃ (xr_Blank_mono hsub₂
            (xr_Blank_mono hsub₁ hbl₀)))) p (by omega) (by omega)
        · rcases le_or_gt p (hk j + wL.length) with h3 | h3
          · exact xr_Blank_mono hsub₅ hbl₄ p (by omega) (by omega)
          · exact hbl₅ p (by omega) (by omega)
    · have h0 : wk j p = none := by
        by_contra hne
        exact hin (hwin p hne)
      exact xr_none_mono hsub₅ (xr_none_mono hsub₄ (xr_none_mono hsub₃ (xr_none_mono hsub₂
        (xr_none_mono hsub₁ (xr_none_mono hsub₀ h0)))))
  have hh : hk j - wL.length - wL.length + wL.length + wL.length + wL.length + wL.length =
      hk j + 2 * wL.length := by ring
  rw [hf, hh] at hrun₅
  refine ⟨T₀ + T₁ + T₂ + T₃ + T₄ + T₅, by omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hrun₀, hrun₁, hrun₂, hrun₃, hrun₄, hrun₅]

/-- **The window clear on the host, from tape `N.k - m` on.** The tapes `N.k - m, …, N.k - 1`,
each with its content within radius `2|wL|` of its head, are blanked within `m·6(2|wL| + 3)` steps,
after which the host is at the increment. -/
private theorem xr_clear_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (ip : Fin (z.length + 2)) (ch ctr cp : ℤ → Option Bool) (wL : List Bool) (hch hctr hcp : ℤ) :
    ∀ (m : ℕ), m ≤ N.k → ∀ (wk : Fin N.k → ℤ → Option Bool) (hk : Fin N.k → ℤ),
      (∀ j : Fin N.k, N.k - m ≤ j.val → xr_Win (wk j) (hk j) (2 * wL.length)) →
      ∃ T ≤ m * (6 * (2 * wL.length + 3)), ∃ hk' : Fin N.k → ℤ,
        (xr_host C).runFrom ⟨some (xr_passStart C a l (N.k - m)), ip,
          xr_tapes wk ch ctr cp (FinTM.bufferTape wL), xr_heads hk hch hctr hcp 0, []⟩ T =
        ⟨some ⟨(.inc, a, l), FlagPhase.run⟩, ip,
          xr_tapes (fun j => if N.k - m ≤ j.val then (fun _ => none) else wk j) ch ctr cp
            (FinTM.bufferTape wL),
          xr_heads hk' hch hctr hcp 0, []⟩ := by
  intro m
  induction m with
  | zero =>
    intro _ wk hk _
    refine ⟨0, Nat.zero_le _, hk, ?_⟩
    rw [MultiTapeTM.runFrom_zero]
    have h1 : xr_passStart C a l (N.k - 0) = ⟨(.inc, a, l), FlagPhase.run⟩ := by
      unfold xr_passStart
      rw [dif_neg (by omega)]
    have h2 : (fun j : Fin N.k => if N.k - 0 ≤ j.val then (fun _ : ℤ => (none : Option Bool))
        else wk j) = wk := by
      funext j
      rw [if_neg (by have := j.isLt; omega)]
    rw [h1, h2]
  | succ m ih =>
    intro hm wk hk hwin
    have hj : N.k - (m + 1) < N.k := by omega
    have hstart : xr_passStart C a l (N.k - (m + 1)) =
        ⟨(.pass ⟨N.k - (m + 1), hj⟩ ⟨0, by omega⟩, a, l), xr_St.run⟩ := by
      unfold xr_passStart
      rw [dif_pos hj]
      rfl
    obtain ⟨T₁, hT₁, hrun₁⟩ := xr_clearTape_host C z a l ip wk ch ctr cp wL hk hch hctr hcp
      ⟨N.k - (m + 1), hj⟩ (hwin _ le_rfl)
    have hnext : (⟨N.k - (m + 1), hj⟩ : Fin N.k).val + 1 = N.k - m := by
      show N.k - (m + 1) + 1 = N.k - m
      omega
    rw [hnext] at hrun₁
    obtain ⟨T₂, hT₂, hk', hrun₂⟩ := ih (by omega) (Function.update wk ⟨N.k - (m + 1), hj⟩
      (fun _ => none))
      (Function.update hk ⟨N.k - (m + 1), hj⟩ (hk ⟨N.k - (m + 1), hj⟩ + 2 * wL.length))
      (by
        intro j hjm
        have hne : j ≠ ⟨N.k - (m + 1), hj⟩ := by
          intro h
          rw [h] at hjm
          change N.k - m ≤ N.k - (m + 1) at hjm
          omega
        rw [Function.update_of_ne hne, Function.update_of_ne hne]
        exact hwin j (by omega))
    have htp : (fun j : Fin N.k => if N.k - m ≤ j.val then (fun _ : ℤ => (none : Option Bool))
        else Function.update wk ⟨N.k - (m + 1), hj⟩ (fun _ => none) j) =
        fun j => if N.k - (m + 1) ≤ j.val then (fun _ => none) else wk j := by
      funext j
      by_cases hjj : j = ⟨N.k - (m + 1), hj⟩
      · rw [hjj, if_neg (by change ¬ (N.k - m ≤ N.k - (m + 1)); omega), Function.update_self,
          if_pos (le_refl _)]
      · rw [Function.update_of_ne hjj]
        by_cases h1 : N.k - m ≤ j.val
        · rw [if_pos h1, if_pos (by omega)]
        · have hne : j.val ≠ N.k - (m + 1) := fun h => hjj (Fin.ext h)
          rw [if_neg h1, if_neg (by omega)]
    have hmul : (m + 1) * (6 * (2 * wL.length + 3)) =
        m * (6 * (2 * wL.length + 3)) + 6 * (2 * wL.length + 3) := by ring
    refine ⟨T₁ + T₂, by omega, hk', ?_⟩
    rw [hstart, MultiTapeTM.runFrom_add, hrun₁, hrun₂, htp]

/-! ##### One cycle -/

/-- The branch along `s` keeps `N`'s tapes within radius `2|s|` of its translated heads. -/
private theorem xr_branch_win {N : FinNDTM Bool} (z s : List Bool) (h : Fin N.k → ℤ)
    (j : Fin N.k) :
    xr_Win ((xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes j)
      ((xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos j) (2 * s.length) := by
  obtain ⟨hpos, hblank, -⟩ := xr_window_runWith N.tm z s
  intro q hq
  have h1 := hpos j
  have h2 : ¬ (s.length : ℤ) < |q - h j| := fun hlt => hq (hblank j (q - h j) hlt)
  rw [abs_le] at h1
  push_neg at h2
  rw [abs_le] at h2
  show (N.tm.runWith s (N.tm.initCfg z)).workTapePos j + h j - 2 * s.length ≤ q ∧
    q ≤ (N.tm.runWith s (N.tm.initCfg z)).workTapePos j + h j + 2 * s.length
  omega

/-- **One cycle on the host.** From the start of a cycle at depth `L = |s|` (the depth word has
value `L` and width `L`, the counter width at most `L`), within `(18 N.k + 19)(L + 1)` steps the
host replays the choice word `s`, folds its verdicts into the flags (the output `[true]` raises
the accept flag, a live branch the live flag), restores the tapes, and either dispatches to the
next cycle on `incFixed s`, or, at the overflow, to the depth's end.

**Proof sketch.** The cycle's phases, joined by the host's dispatches: copy the depth word onto
the counter (`xr_copy_host`, `2|wL| + 3` steps); replay the choice word `s` on `N`'s tapes from
the represented start (`xr_replay_host`), recording the branch's liveness in the live flag; test
the captured output, raising the accept flag on `[true]` (`xr_test_host`); rewind the choice word
(`xr_crewind_host`) and the input head (`xr_irewind_host`); clear `N`'s tapes within radius
`2|s|` of their translated heads (`xr_clear_host`, the radius by `xr_branch_win`); and increment
the choice word, to the next cycle on `incFixed s = some s'` (`xr_inc_host_succ`) or to the
depth's end at the overflow (`xr_inc_host_overflow`). The clear costs `N.k·6(2L + 3)`, and the
phases together at most `(18 N.k + 19)(L + 1)`. -/
private theorem xr_cycle_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (wL s u : List Bool) (h : Fin N.k → ℤ) (hval : xr_val wL = s.length)
    (hL : wL.length = s.length) (hu : u.length ≤ wL.length) :
    ∃ T ≤ (18 * N.k + 19) * (s.length + 1), ∃ u' : List Bool, u'.length ≤ wL.length ∧
      ∃ h' : Fin N.k → ℤ,
      (∀ s', incFixed s = some s' →
        (xr_host C).runFrom (xr_cycle C z a l wL s u h) T =
          xr_cycle C z (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
            (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) wL s' u' h') ∧
      (incFixed s = none →
        (xr_host C).runFrom (xr_cycle C z a l wL s u h) T =
          xr_depthEnd C z (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
            (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) s.length wL u' h') := by
  obtain ⟨-, -, hout⟩ := xr_window_runWith N.tm z s
  have hip := xr_branch_inputPos_le (N := N) z s
  have h1 := xr_copy_host C z a l wL s u h hu
  obtain ⟨T₂, hT₂, p, hp, w', hw', h2⟩ := xr_replay_host C z a l wL s h hval
  obtain ⟨T₃, hT₃, h3⟩ := xr_test_host C z a (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome)
    (N.tm.runWith s (N.tm.initCfg z)).inputPos
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes (FinTM.bufferTape s)
    (FinTM.bufferTape w') (FinTM.bufferTape wL)
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p 0 0
    (N.tm.runWith s (N.tm.initCfg z)).output
  obtain ⟨T₄, hT₄, h4⟩ := xr_crewind_host C z
    (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
    (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome)
    (N.tm.runWith s (N.tm.initCfg z)).inputPos
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes s (FinTM.bufferTape w')
    (FinTM.bufferTape []) (FinTM.bufferTape wL)
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos p hp 0 0 0
  obtain ⟨T₅, hT₅, h5⟩ := xr_irewind_host C z
    (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
    (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome)
    (N.tm.runWith s (N.tm.initCfg z)).inputPos
    (xr_tapes (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes (FinTM.bufferTape s)
      (FinTM.bufferTape w') (FinTM.bufferTape []) (FinTM.bufferTape wL))
    (xr_heads (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos 0 0 0 0)
  rw [xr_firstPass_eq] at h5
  obtain ⟨T₆, hT₆, hk', h6⟩ := xr_clear_host C z
    (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
    (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) 1 (FinTM.bufferTape s)
    (FinTM.bufferTape w') (FinTM.bufferTape []) wL 0 0 0 N.k le_rfl
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes
    (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapePos
    (fun j _ => by rw [hL]; exact xr_branch_win z s h j)
  rw [Nat.sub_self] at h6
  have hblank : (fun j : Fin N.k => if 0 ≤ j.val then (fun _ : ℤ => (none : Option Bool))
      else (xr_shift h (N.tm.runWith s (N.tm.initCfg z))).workTapes j) = fun _ _ => none := by
    funext j
    rw [if_pos (Nat.zero_le _)]
  rw [hblank] at h6
  have hchain : ∀ T₇, (xr_host C).runFrom (xr_cycle C z a l wL s u h)
      (2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + T₇) =
      (xr_host C).runFrom ⟨some ⟨(.inc,
        a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]),
        l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape w') (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads hk' 0 0 0 0, []⟩ T₇ := by
    intro T₇
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, h1, h2, h3, h4, h5,
      h6]
  have hbound : 2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + (2 * s.length + 3) ≤
      (18 * N.k + 19) * (s.length + 1) := by
    have e1 : N.k * (6 * (2 * wL.length + 3)) = 12 * (N.k * s.length) + 18 * N.k := by
      rw [hL]
      ring
    have e2 : (18 * N.k + 19) * (s.length + 1) =
        18 * (N.k * s.length) + 18 * N.k + 19 * s.length + 19 := by
      ring
    omega
  rcases hs : incFixed s with _ | s'
  · -- the overflow
    have h7 := xr_inc_host_overflow C z
      (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
      (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) wL s w' hs hk'
    refine ⟨2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + (2 * s.length + 3), hbound, w', hw'.le,
      hk',
      (fun s' hs' => nomatch hs'), fun _ => ?_⟩
    rw [hchain, h7]
  · -- a successor
    obtain ⟨T₇, hT₇, h7⟩ := xr_inc_host_succ C z
      (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
      (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) wL s s' w' hs hk'
    refine ⟨2 * wL.length + 3 + T₂ + T₃ + T₄ + T₅ + T₆ + T₇, by omega, w', hw'.le, hk',
      fun s'' hs'' => ?_, (fun h0 => nomatch h0)⟩
    rw [Option.some.injEq] at hs''
    subst hs''
    rw [hchain, h7]

/-! #### One depth, the depth change -/

/-- **One depth on the host.** From the cycle at the word `s`, with `m = 2^L - val s` words of
depth `L` left to replay, the host runs through them to the depth's end within
`m·(18 N.k + 19)(L + 1)` steps; the accept flag ends up raised exactly when it was, or some word
of value at least `val s` outputs `[true]`, and the live flag exactly when it was, or some such
word is live after `L` steps.

**Proof sketch.** Induction on `m`. At `m = 0` there is nothing to show, since `val s < 2^L`.
Otherwise run one cycle (`xr_cycle_host`). If `s` is the depth's last word (`incFixed s = none`),
the cycle ends at the depth's end, and `s` is the only word of length `L` with value at least
`val s` (`xr_incFixed_none_max`, `xr_val_inj`), which gives both flags. Otherwise the cycle
continues at `s' = incFixed s`, with `val s' = val s + 1`, and the induction hypothesis at `s'`
with the updated flags gives the rest: a word of value at least `val s` is `s` itself or has
value at least `val s'`. -/
private theorem xr_depth_host {N : FinNDTM Bool} (C : xr_Clock N) (z wL : List Bool) (L : ℕ)
    (hL : wL.length = L) (hval : xr_val wL = L) :
    ∀ (m : ℕ) (a l : Bool) (s u : List Bool) (h : Fin N.k → ℤ), s.length = L → u.length ≤ L →
      2 ^ L - xr_val s = m →
      ∃ T ≤ m * ((18 * N.k + 19) * (L + 1)), ∃ (a' l' : Bool) (u' : List Bool) (h' : Fin N.k → ℤ),
        (xr_host C).runFrom (xr_cycle C z a l wL s u h) T = xr_depthEnd C z a' l' L wL u' h' ∧
        u'.length ≤ L ∧
        (a' = true ↔ a = true ∨ ∃ s', s'.length = L ∧ xr_val s ≤ xr_val s' ∧
          (N.tm.runWith s' (N.tm.initCfg z)).output = [true]) ∧
        (l' = true ↔ l = true ∨ ∃ s', s'.length = L ∧ xr_val s ≤ xr_val s' ∧
          (N.tm.runWith s' (N.tm.initCfg z)).state ≠ none) := by
  intro m
  induction m with
  | zero =>
    intro a l s u h hs hu hm
    exfalso
    have := xr_val_lt s
    rw [hs] at this
    omega
  | succ m ih =>
    intro a l s u h hs hu hm
    obtain ⟨T₁, hT₁, u₁, hu₁, h₁, hsucc, hover⟩ := xr_cycle_host C z a l wL s u h
      (hval.trans hs.symm) (hL.trans hs.symm) (hu.trans hL.symm.le)
    rw [hs] at hT₁
    rcases hinc : incFixed s with _ | s'
    · -- `s` is the depth's last word
      have hmax : ∀ s', s'.length = L → xr_val s ≤ xr_val s' → s' = s := fun s' hs' hle =>
        xr_val_inj (hs'.trans hs.symm)
          (le_antisymm (xr_incFixed_none_max hinc (hs'.trans hs.symm)) hle)
      refine ⟨T₁, hT₁.trans (Nat.le_mul_of_pos_left _ (by omega)),
        a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]),
        l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome, u₁, h₁, ?_, hu₁.trans hL.le, ?_,
        ?_⟩
      · rw [hover hinc, hs]
      · rw [Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro (h0 | h0)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
        · rintro (h0 | ⟨s', hs', hle, hout⟩)
          · exact Or.inl h0
          · rw [hmax s' hs' hle] at hout
            exact Or.inr hout
      · rw [Bool.or_eq_true, Option.isSome_iff_ne_none]
        constructor
        · rintro (h0 | h0)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
        · rintro (h0 | ⟨s', hs', hle, hlive⟩)
          · exact Or.inl h0
          · rw [hmax s' hs' hle] at hlive
            exact Or.inr hlive
    · -- `s'` follows `s`
      have hs' : s'.length = L := (incFixed_length hinc).trans hs
      have hv' : xr_val s' = xr_val s + 1 := xr_incFixed_val hinc
      have hlt := xr_val_lt s'
      rw [hs'] at hlt
      obtain ⟨T₂, hT₂, a', l', u', h', hrun₂, hu', ha', hl'⟩ := ih
        (a || decide ((N.tm.runWith s (N.tm.initCfg z)).output = [true]))
        (l || (N.tm.runWith s (N.tm.initCfg z)).state.isSome) s' u₁ h₁ hs'
        (hu₁.trans hL.le) (by omega)
      have hmul : (m + 1) * ((18 * N.k + 19) * (L + 1)) =
          m * ((18 * N.k + 19) * (L + 1)) + (18 * N.k + 19) * (L + 1) := by ring
      refine ⟨T₁ + T₂, by omega, a', l', u', h', ?_, hu', ?_, ?_⟩
      · rw [MultiTapeTM.runFrom_add, hsucc s' hinc, hrun₂]
      · rw [ha', Bool.or_eq_true, decide_eq_true_eq]
        constructor
        · rintro ((h0 | h0) | ⟨s'', hs'', hle, hout⟩)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
          · exact Or.inr ⟨s'', hs'', by omega, hout⟩
        · rintro (h0 | ⟨s'', hs'', hle, hout⟩)
          · exact Or.inl (Or.inl h0)
          · rcases Nat.lt_or_ge (xr_val s) (xr_val s'') with hlt' | hge
            · exact Or.inr ⟨s'', hs'', by omega, hout⟩
            · have hss : s'' = s := xr_val_inj (hs''.trans hs.symm) (le_antisymm hge hle)
              subst hss
              exact Or.inl (Or.inr hout)
      · rw [hl', Bool.or_eq_true, Option.isSome_iff_ne_none]
        constructor
        · rintro ((h0 | h0) | ⟨s'', hs'', hle, hlive⟩)
          · exact Or.inl h0
          · exact Or.inr ⟨s, hs, le_rfl, h0⟩
          · exact Or.inr ⟨s'', hs'', by omega, hlive⟩
        · rintro (h0 | ⟨s'', hs'', hle, hlive⟩)
          · exact Or.inl (Or.inl h0)
          · rcases Nat.lt_or_ge (xr_val s) (xr_val s'') with hlt' | hge
            · exact Or.inr ⟨s'', hs'', by omega, hlive⟩
            · have hss : s'' = s := xr_val_inj (hs''.trans hs.symm) (le_antisymm hge hle)
              subst hss
              exact Or.inl (Or.inr hlive)

/-- **The choice word's extension on the host**: within `2|s| + 3` steps a `false` is appended to
the choice word and the host dispatches to the depth word's extension. -/
private theorem xr_extC_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (s u wL : List Bool) (h : Fin N.k → ℤ) :
    ∃ T ≤ 2 * s.length + 3,
      (xr_host C).runFrom (⟨some ⟨(.extC, a, l), xr_St.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
            Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) T =
      ⟨some ⟨(.extD, a, l), xr_St.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape (s ++ [false])) (FinTM.bufferTape u)
          (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ := by
  have hrun := xr_extendTM_run (xr_choice N.k) s
    (⟨some xr_St.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool xr_St z) rfl (xr_tapes_choice _ _ _ _ _) (xr_heads_choice _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_extendTM (N.k + 2 + 2) (xr_choice N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.extC, a, l) xr_St.run 1 _ _ T' _ hrun' _ rfl rfl
    ⟨(.extD, a, l), xr_St.run⟩ rfl
    (fun u hu s hs => xr_red_leaf_none C (.extC, a, l)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨a, l, rfl⟩))))) s (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_tapes_upd_choice, xr_heads_upd_choice]

/-- **The depth word's extension on the host**: within `2|wL| + 3` steps a `false` is appended to
the depth word and the host dispatches to its increment. -/
private theorem xr_extD_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (s u wL : List Bool) (h : Fin N.k → ℤ) :
    ∃ T ≤ 2 * wL.length + 3,
      (xr_host C).runFrom (⟨some ⟨(.extD, a, l), xr_St.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
            Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) T =
      ⟨some ⟨(.incD, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape (wL ++ [false])), xr_heads h 0 0 0 0, []⟩ := by
  have hrun := xr_extendTM_run (xr_dep N.k) wL
    (⟨some xr_St.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool xr_St z) rfl (xr_tapes_dep _ _ _ _ _) (xr_heads_dep _ _ _ _ _)
  obtain ⟨T', hT', hrun', hguard⟩ := xr_firstArrival' (xr_extendTM (N.k + 2 + 2) (xr_dep N.k))
    (fun s => ∃ b, s = .done b) (xr_done_stationary _ (fun b inp w => rfl)) hrun rfl ⟨_, rfl⟩
  refine ⟨T' + 1, by omega, ?_⟩
  rw [xr_phase_step C (.extD, a, l) xr_St.run 1 _ _ T' _ hrun' _ rfl rfl
    ⟨(.incD, a, l), FlagPhase.run⟩ rfl
    (fun u hu s hs => xr_red_leaf_none C (.extD, a, l)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨a, l, rfl⟩))))) s (hguard u hu s hs) rfl)]
  dsimp only
  rw [xr_tapes_upd_dep, xr_heads_upd_dep]

/-- **The depth word's increment on the host**: with `incFixed w = some w'`, within `2|w| + 3` steps
the depth tape holds `w'` and the host dispatches to the next depth's first cycle. -/
private theorem xr_incD_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a l : Bool)
    (s u w w' : List Bool) (hw' : incFixed w = some w') (h : Fin N.k → ℤ) :
    ∃ T ≤ 2 * w.length + 3,
      (xr_host C).runFrom (⟨some ⟨(.incD, a, l), FlagPhase.run⟩, 1,
        xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u) (FinTM.bufferTape [])
          (FinTM.bufferTape w), xr_heads h 0 0 0 0, []⟩ :
            Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) T = xr_cycle C z a l w' s u h := by
  obtain ⟨hcfg, hguard, -⟩ := incrementTM_run_succ_ofCfg (xr_dep N.k) w w' hw'
    (⟨some FlagPhase.run, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape s) (FinTM.bufferTape u)
      (FinTM.bufferTape []) (FinTM.bufferTape w), xr_heads h 0 0 0 0, []⟩ :
      Cfg (N.k + 2 + 2) Bool FlagPhase z) rfl
    (by intro p _ _; dsimp only; rw [xr_tapes_dep, xr_heads_dep, zero_add])
  refine ⟨2 * (w.takeWhile id).length + 2 + 1, by
    have := (List.takeWhile_sublist (l := w) id).length_le; omega, ?_⟩
  rw [xr_phase_step C (.incD, a, l) FlagPhase.run 1 _ _ _ _ hcfg (FlagPhase.done true) rfl rfl
    ⟨(.copy, a, l), SweepPhase.sweep⟩ rfl
    (fun t ht s hs => by
      cases s with
      | done b => exact absurd hs (hguard t ht b)
      | run => rfl
      | rewind b => rfl)]
  dsimp only
  rw [xr_patch_eq _ _ (xr_dep N.k) (xr_heads_dep _ _ _ _ _) w w' w (incFixed_length hw')
    (xr_tapes_dep _ _ _ _ _) le_rfl, xr_tapes_upd_dep]
  rfl

/-- **The depth change on the host.** From a depth's end with the live flag up, within `6L + 11`
steps the host extends the choice word to the all-`false` word of length `L + 1`, extends and
increments the depth word to a word of width and value `L + 1`, lowers both flags, and starts
the next depth's first cycle. -/
private theorem xr_deepen_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (a : Bool)
    (L : ℕ) (wL u : List Bool) (h : Fin N.k → ℤ) (hL : wL.length = L) (hval : xr_val wL = L) :
    ∃ T ≤ 6 * L + 11, ∃ wL' : List Bool, wL'.length = L + 1 ∧ xr_val wL' = L + 1 ∧
      (xr_host C).runFrom (xr_depthEnd C z a true L wL u h) T =
        xr_cycle C z false false wL' (List.replicate (L + 1) false) u h := by
  obtain ⟨T₁, hT₁, h1⟩ := xr_extC_host C z false false (List.replicate L false) u wL h
  obtain ⟨T₂, hT₂, h2⟩ := xr_extD_host C z false false (List.replicate L false ++ [false]) u wL h
  obtain ⟨wL', hwL'⟩ := xr_incFixed_append_false wL
  obtain ⟨T₃, hT₃, h3⟩ := xr_incD_host C z false false (List.replicate L false ++ [false]) u
    (wL ++ [false]) wL' hwL' h
  have hlen : (wL ++ [false]).length = L + 1 := by simp [hL]
  refine ⟨T₁ + T₂ + T₃, by rw [List.length_replicate] at hT₁; rw [hlen] at hT₃; omega, wL',
    (incFixed_length hwL').trans hlen, by rw [xr_incFixed_val hwL', xr_val_append_false, hval], ?_⟩
  rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add]
  show (xr_host C).runFrom ((xr_host C).runFrom ((xr_host C).runFrom ⟨some ⟨(.extC, false, false),
    xr_St.run⟩, 1, xr_tapes (fun _ _ => none) (FinTM.bufferTape (List.replicate L false))
      (FinTM.bufferTape u) (FinTM.bufferTape []) (FinTM.bufferTape wL), xr_heads h 0 0 0 0, []⟩ T₁)
      T₂) T₃ = _
  rw [h1, h2, h3, ← List.replicate_succ']

/-! #### The whole run, the machine `E`, the answer -/

/-- The halt phase's `start` is stationary on the host: the table redirects it to itself. -/
private theorem xr_halt_fixed {N : FinNDTM Bool} (C : xr_Clock N) {z : List Bool}
    (d : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) (a l : Bool)
    (hd : d.state = some ⟨(.halt, a, l), xr_St.start⟩) : (xr_host C).step d = d := by
  have hhost := (phaseHostTM_run (xr_M C) ⟨(.copy, false, false), SweepPhase.sweep⟩ (xr_red C)
    (.halt, a, l) (⟨some xr_St.start, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
      Cfg (N.k + 2 + 2) Bool (xr_PhSt C (.halt, a, l)) z) _ 0 MultiTapeTM.runFrom_zero
    xr_St.start rfl ⟨(.halt, a, l), xr_St.start⟩ rfl
    (fun u hu => absurd hu (Nat.not_lt_zero u))).2
  rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero] at hhost
  have hd' : (⟨some xr_St.start, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
      Cfg (N.k + 2 + 2) Bool (xr_PhSt C (.halt, a, l)) z).mapState (Sigma.mk (.halt, a, l)) =
        d :=
    Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  have hd'' : (⟨some xr_St.start, d.inputPos, d.workTapes, d.workTapePos, d.output⟩ :
      Cfg (N.k + 2 + 2) Bool (xr_PhSt C (.halt, a, l)) z).mapState
        (fun _ => (⟨(.halt, a, l), xr_St.start⟩ : Σ i, xr_PhSt C i)) = d :=
    Cfg.mapState_eq_of_fields _ _ _ (by rw [hd]; rfl) rfl rfl rfl rfl
  rw [hd', hd''] at hhost
  exact hhost

open Classical in
/-- **The depths on the host.** With `L*` the first all-halting depth, from the first cycle at a
depth `L ≤ L*` (the depth word of width and value `L`, the choice word all `false`, the counter
word of width at most `L`, both flags down), within `Σ_{i ≤ L* - L} 2^{L+i}·(18 N.k + 38)(L+i+1)`
steps the host reaches the depth `L*`'s end, the live flag down and the accept flag
`decide (N.AcceptsWithin z L*)`: every depth below `L*` has a live branch and deepens, and the
depth `L*` answers.

**Proof sketch.** Induction on `m = L* − L`. At `L = L*`, one depth from the all-`false` word
(`xr_depth_host`, `2^{L*}` cycles) ends with the live flag down, since every branch of length
`L*` has halted, and the accept flag up exactly when some branch of length `L*` outputs `[true]`,
that is `N.AcceptsWithin z L*` (`FinNDTM.acceptsWithin_iff`). Below `L*`, minimality gives a
live branch of length `L`, so the depth ends with the live flag up; `xr_deepen_host` (at most
`6L + 11` steps, inside the depth's `2^L·19(L + 1)` slack) starts depth `L + 1`, and the
induction hypothesis finishes. -/
private theorem xr_run_host {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) (Ls : ℕ)
    (hLs : N.tm.HaltsWithin z Ls) (hmin : ∀ L' < Ls, ¬ N.tm.HaltsWithin z L') :
    ∀ (m L : ℕ) (wL u : List Bool) (h : Fin N.k → ℤ), L + m = Ls → wL.length = L →
      xr_val wL = L → u.length ≤ L →
      ∃ T ≤ ∑ i ∈ Finset.range (m + 1), 2 ^ (L + i) * ((18 * N.k + 38) * (L + i + 1)),
        ∃ (wL' u' : List Bool) (h' : Fin N.k → ℤ),
          (xr_host C).runFrom (xr_cycle C z false false wL (List.replicate L false) u h) T =
            xr_depthEnd C z (decide (N.AcceptsWithin z Ls)) false Ls wL' u' h' := by
  intro m
  induction m with
  | zero =>
    intro L wL u h hLm hL hval hu
    have hLm' : L = Ls := by omega
    rw [hLm'] at hL hval hu
    rw [hLm']
    obtain ⟨T₁, hT₁, a', l', u', h', hrun, -, ha', hl'⟩ := xr_depth_host C z wL Ls hL hval
      (2 ^ Ls) false false (List.replicate Ls false) u h (by simp) hu
      (by rw [xr_val_replicate_false, Nat.sub_zero])
    have hl'' : l' = false := by
      cases l' with
      | false => rfl
      | true =>
        exfalso
        rcases hl'.mp rfl with h0 | ⟨s', hs', -, hlive⟩
        · exact Bool.false_ne_true h0
        · exact hlive (NDTM.haltsWithin_iff.mp hLs s' hs')
    have ha'' : a' = decide (N.AcceptsWithin z Ls) := by
      rw [Bool.eq_iff_iff, decide_eq_true_iff, ha']
      constructor
      · rintro (h0 | ⟨s', hs', -, hout⟩)
        · exact absurd h0 Bool.false_ne_true
        · exact FinNDTM.acceptsWithin_iff.mpr ⟨s', hs', NDTM.haltsWithin_iff.mp hLs s' hs', hout⟩
      · intro hacc
        obtain ⟨w, hw, -, hout⟩ := FinNDTM.acceptsWithin_iff.mp hacc
        exact Or.inr ⟨w, hw, by rw [xr_val_replicate_false]; exact Nat.zero_le _, hout⟩
    subst hl'' ha''
    refine ⟨T₁, ?_, wL, u', h', hrun⟩
    simp only [Nat.zero_add, Nat.add_zero, Finset.sum_range_one]
    exact hT₁.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega)))
  | succ m ih =>
    intro L wL u h hLm hL hval hu
    have hnot := hmin L (by omega)
    rw [NDTM.haltsWithin_iff] at hnot
    push_neg at hnot
    obtain ⟨s₀, hs₀, hlive⟩ := hnot
    obtain ⟨T₁, hT₁, a', l', u', h', hrun₁, hu', -, hl'⟩ := xr_depth_host C z wL L hL hval
      (2 ^ L) false false (List.replicate L false) u h (by simp) hu
      (by rw [xr_val_replicate_false, Nat.sub_zero])
    have hl'' : l' = true :=
      hl'.mpr (Or.inr ⟨s₀, hs₀, by rw [xr_val_replicate_false]; exact Nat.zero_le _, hlive⟩)
    subst hl''
    obtain ⟨T₂, hT₂, wL', hwL'len, hwL'val, hrun₂⟩ := xr_deepen_host C z a' L wL u' h' hL hval
    obtain ⟨T₃, hT₃, wL'', u'', h'', hrun₃⟩ := ih (L + 1) wL' u' h' (by omega) hwL'len hwL'val
      (hu'.trans (Nat.le_succ L))
    refine ⟨T₁ + T₂ + T₃, ?_, wL'', u'', h'', ?_⟩
    · rw [Finset.sum_range_succ']
      have hshift : ∑ i ∈ Finset.range (m + 1),
          2 ^ (L + (i + 1)) * ((18 * N.k + 38) * (L + (i + 1) + 1)) =
          ∑ i ∈ Finset.range (m + 1), 2 ^ (L + 1 + i) * ((18 * N.k + 38) * (L + 1 + i + 1)) :=
        Finset.sum_congr rfl (fun i _ => by rw [show L + (i + 1) = L + 1 + i by omega])
      have hlast : 2 ^ (L + 0) * ((18 * N.k + 38) * (L + 0 + 1)) =
          2 ^ L * ((18 * N.k + 38) * (L + 1)) := rfl
      have h19 : 6 * L + 11 ≤ 2 ^ L * (19 * (L + 1)) := by
        have := Nat.le_mul_of_pos_left (19 * (L + 1)) (Nat.two_pow_pos L)
        omega
      have hsplit : 2 ^ L * ((18 * N.k + 38) * (L + 1)) =
          2 ^ L * ((18 * N.k + 19) * (L + 1)) + 2 ^ L * (19 * (L + 1)) := by ring
      omega
    · rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add, hrun₁, hrun₂, hrun₃]

/-- The blank tape bank. -/
private theorem xr_tapes_blank (k : ℕ) :
    xr_tapes (k := k) (fun _ _ => none) (fun _ => none) (fun _ => none) (fun _ => none)
      (fun _ => none) = fun _ _ => none :=
  xr_bank_ext _ _ (fun j => xr_tapes_work _ _ _ _ _ j) (xr_tapes_choice _ _ _ _ _)
    (xr_tapes_ctr _ _ _ _ _) (xr_tapes_cap _ _ _ _ _) (xr_tapes_dep _ _ _ _ _)

/-- The heads at the origin. -/
private theorem xr_heads_zero (k : ℕ) : xr_heads (k := k) (fun _ => 0) 0 0 0 0 = fun _ => 0 :=
  xr_bank_ext _ _ (fun j => xr_heads_work _ _ _ _ _ j) (xr_heads_choice _ _ _ _ _)
    (xr_heads_ctr _ _ _ _ _) (xr_heads_cap _ _ _ _ _) (xr_heads_dep _ _ _ _ _)

/-- The host's halt anchor with the accept flag `b`. -/
private def xr_anchor {N : FinNDTM Bool} (C : xr_Clock N) (b : Bool) : Σ i, xr_PhSt C i :=
  ⟨(.halt, b, false), xr_St.start⟩

/-- The two-exit seam of the host onto the two one-step answers: at the anchor with the accept
flag up, the answer `[true]`; at the anchor with it down, the answer `[false]`. -/
private noncomputable def xr_seam {N : FinNDTM Bool} (C : xr_Clock N) :
    MultiTapeTM (N.k + 2 + 2) Bool (((Σ i, xr_PhSt C i) ⊕ xr_St) ⊕ xr_St) :=
  seamCompTM₂ (xr_host C) (xr_anchor C true) (xr_anchor C false)
    (xr_answerTM (N.k + 2 + 2) true) xr_St.start (xr_answerTM (N.k + 2 + 2) false) xr_St.start

/-- **The exhaustive replay's machine `E`**: the seam, started at the host's first cycle. -/
private noncomputable def xr_E {N : FinNDTM Bool} (C : xr_Clock N) : FinTM Bool :=
  ⟨N.k + 2 + 2, ((Σ i, xr_PhSt C i) ⊕ xr_St) ⊕ xr_St,
    { xr_seam C with q₀ := Sum.inl (Sum.inl ⟨(.copy, false, false), SweepPhase.sweep⟩) }⟩

/-- `E`'s initial configuration on `z` is the host's first cycle at depth `0`, in the seam's
states. -/
private theorem xr_E_initCfg {N : FinNDTM Bool} (C : xr_Clock N) (z : List Bool) :
    (xr_E C).tm.initCfg z =
      ((xr_cycle C z false false [] [] [] (fun _ => 0)).mapState Sum.inl).mapState Sum.inl := by
  refine (MultiTapeTM.initCfg_with_q₀ (xr_seam C)
    (Sum.inl (Sum.inl ⟨(.copy, false, false), SweepPhase.sweep⟩)) z).trans ?_
  apply Cfg.ext
  · rw [Cfg.init_state, Cfg.mapState_state, Cfg.mapState_state]; rfl
  · rw [Cfg.init_inputPos, Cfg.mapState_inputPos, Cfg.mapState_inputPos]; rfl
  · funext j p
    simp only [Cfg.init_workTapes, Cfg.mapState_workTapes]
    show none = xr_tapes (fun _ _ => none) (FinTM.bufferTape []) (FinTM.bufferTape [])
      (FinTM.bufferTape []) (FinTM.bufferTape []) j p
    rw [FinTM.bufferTape_nil, xr_tapes_blank]
  · funext j
    simp only [Cfg.init_workTapePos, Cfg.mapState_workTapePos]
    show (0 : ℤ) = xr_heads (fun _ => 0) 0 0 0 0 j
    rw [xr_heads_zero]
  · rw [Cfg.init_output, Cfg.mapState_output, Cfg.mapState_output]; rfl

/-- **The answer's tail.** From a live configuration with empty output, one step of the answer
row halts with the output `[b]`, read in any renaming of the states. -/
private theorem xr_answer_tail {K : ℕ} {x : List Bool} {S S' : Type} (b : Bool)
    (d : Cfg K Bool S x) (q : S) (hd : d.state = some q) (hout : d.output = [])
    (f : xr_St → S') :
    (((xr_answerTM K b).runFrom (d.mapState fun _ => xr_St.start) 1).mapState f).state = none ∧
    (((xr_answerTM K b).runFrom (d.mapState fun _ => xr_St.start) 1).mapState f).output = [b] := by
  rw [xr_answerTM_run b (d.mapState fun _ => xr_St.start) xr_St.start
    (by rw [Cfg.mapState_state, hd]; rfl)]
  refine ⟨?_, ?_⟩
  · rw [Cfg.mapState_state]; rfl
  · rw [Cfg.mapState_output]
    show (d.mapState fun _ => xr_St.start).output ++ [b] = [b]
    rw [Cfg.mapState_output, hout, List.nil_append]

/-- **The exhaustive replay `E`.** For every bundled binary NDTM `N` there is a deterministic
machine `E` and a constant `C` such that, on every input `z` on which every branch of `N` of
length `T` has halted (any `T`, which nobody needs to compute), `E` outputs `[true]` if `N`
accepts `z` within `T`, and `[false]` otherwise, in either case within `C·2^{C·(T + 1)}` steps.
There is no `|z|` term. [AB09, §3.2, proof of Theorem 3.2: the trivial exponential simulation
of a nondeterministic machine]

**Proof sketch.** Iterative deepening, on one phase host (`Turing.phaseHostTM`) whose control
carries two flags, "accept" and "live", both down at the start. At depth `L = 0, 1, …` a depth
tape holds a word of width `L` and binary value `L`, and the choice tape runs through the `2^L`
words of length `L`, from all-`false` to overflow (`Turing.incrementTM`). One cycle per word
`s`: copy the depth word onto the clock's counter (`Turing.copyTM`); replay `s` through
`N.tm.replayTM` for `L` steps under the step clock (`Turing.exists_stepClockTMVia`), silently,
with `N`'s output captured (`Turing.embedSilentTM`), raising the live flag if the branch is
still live after `L` steps; test the captured output, raising the accept flag if it is exactly
`[true]`, whether or not the branch has halted, and clear it; rewind the choice head and the
input head; clear `N`'s work tapes; increment the choice word.

The clear does not return the work heads to their origins. Branches commute with translating
the work tapes, so a replay from blank tapes with displaced heads is the branch from
`N.tm.initCfg z`, translated, and the replay lemma (`Turing.NDTM.replayTM_runFrom`) serves from
wherever the last clear left the heads. After `L` steps a work tape's content and its head lie
within `L` of the head's start, so the content lies within `2L` of the final head. Six passes,
each moving the head `L` cells with the depth word as the ruler (two leftward, then four
rightward), blank `[head - 2L, head + 2L]`, hence the whole tape, and leave the head `2L` cells
to the right of where the replay left it.

At the overflow, if the live flag is up, the host lowers both flags, extends the choice word to
the all-`false` word of length `L + 1` and the depth word to width and value `L + 1`, and starts
depth `L + 1`; otherwise it stops, and `E` outputs `[true]` or `[false]` as the accept flag is up
or down (`Turing.seamCompTM₂` onto two one-step answer rows). So `E` stops at the first
all-halting depth `L*`, without computing `T`: `L* ≤ T`, and `L* ≥ 1` since the branch of
length `0` is live. Below `L*` some branch is live, so every such depth ends in a deepening,
which discards both flags: an accept flag raised by a live branch never reaches the answer. At
`L*` every branch has halted, so the accept flag is acceptance within `L*`, which agrees with
acceptance within `T` (`Turing.FinNDTM.AcceptsWithin.mono` one way; the other by truncating an
accepting word of length `T` at `L*`, `Turing.NDTM.runWith_of_halt`).

Ledger. A replay moves the input head at most `L` cells from its start, so the input rewind
costs at most `L + 4` steps and no phase has a `|z|` term. A cycle costs at most
`(18·N.k + 19)(L + 1)` steps and the deepening at most `6L + 11 ≤ 2^L·19(L + 1)`, so depth `L`
costs at most `2^L·(18·N.k + 38)(L + 1)`. With one step to dispatch to the answer row and one
to answer, `Σ_{L ≤ L*} 2^L·(18·N.k + 38)(L + 1) + 2 ≤ C·2^{C·(L* + 1)} ≤ C·2^{C·(T + 1)}` for
`C = 18·N.k + 41`. -/
theorem FinNDTM.exists_exhaustiveDecider (N : FinNDTM Bool) :
    ∃ (E : FinTM Bool) (C : ℕ), ∀ (z : List Bool) (T : ℕ), N.tm.HaltsWithin z T →
      (N.AcceptsWithin z T → E.ComputesInTime z [true] (C * 2 ^ (C * (T + 1)))) ∧
      (¬N.AcceptsWithin z T → E.ComputesInTime z [false] (C * 2 ^ (C * (T + 1)))) := by
  classical
  obtain ⟨C⟩ := xr_Clock.exists N
  refine ⟨xr_E C, 18 * N.k + 41, fun z T hT => ?_⟩
  obtain ⟨Ls, -, hLsT, hLs, hmin, hiff⟩ := xr_first_depth N z T hT
  obtain ⟨T₀, hT₀, wL', u', h', hrun⟩ := xr_run_host C z Ls hLs hmin Ls 0 [] [] (fun _ => 0)
    (Nat.zero_add Ls) rfl xr_val_nil (Nat.zero_le 0)
  rw [List.replicate_zero] at hrun
  simp only [Nat.zero_add] at hT₀
  -- the time: the ledger over the depths `0, …, L*`, then the dispatch and the answer
  have hled := xr_ledger (18 * N.k + 38) Ls
  rw [show 18 * N.k + 38 + 3 = 18 * N.k + 41 by omega] at hled
  have hpow : (18 * N.k + 41) * 2 ^ ((18 * N.k + 41) * (Ls + 1)) ≤
      (18 * N.k + 41) * 2 ^ ((18 * N.k + 41) * (T + 1)) :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left _ (by omega)))
  -- `E`'s run, read through the seam
  have hE : ∀ t, (xr_E C).tm.runFrom ((xr_E C).tm.initCfg z) t =
      (seamCompTM₂ (xr_host C) (xr_anchor C true) (xr_anchor C false)
        (xr_answerTM (N.k + 2 + 2) true) xr_St.start (xr_answerTM (N.k + 2 + 2) false)
        xr_St.start).runFrom
        (((xr_cycle C z false false [] [] [] (fun _ => 0)).mapState Sum.inl).mapState Sum.inl)
        t :=
    fun t => (congrArg (fun c => (xr_E C).tm.runFrom c t) (xr_E_initCfg C z)).trans
      (MultiTapeTM.runFrom_with_q₀ (xr_seam C) _ _ t)
  have hstat : ∀ (d : Cfg (N.k + 2 + 2) Bool (Σ i, xr_PhSt C i) z) q, d.state = some q →
      (q = xr_anchor C true ∨ q = xr_anchor C false) → (xr_host C).step d = d := by
    rintro d q hd (rfl | rfl)
    · exact xr_halt_fixed C d true false hd
    · exact xr_halt_fixed C d false false hd
  have he : xr_anchor C true ≠ xr_anchor C false := fun h =>
    Bool.false_ne_true (congrArg (fun q : Σ i, xr_PhSt C i => q.1.2.1) h).symm
  -- the answer, for either value of the accept flag
  have key : ∀ b, decide (N.AcceptsWithin z Ls) = b →
      (xr_E C).ComputesInTime z [b] ((18 * N.k + 41) * 2 ^ ((18 * N.k + 41) * (T + 1))) := by
    intro b hb
    rw [hb] at hrun
    have hend : (xr_depthEnd C z b false Ls wL' u' h').state = some (xr_anchor C b) := rfl
    have hA : xr_anchor C b = xr_anchor C true ∨ xr_anchor C b = xr_anchor C false := by
      cases b
      exacts [Or.inr rfl, Or.inl rfl]
    obtain ⟨T₁, hT₁, hrun₁, hcut⟩ := xr_firstArrival' (xr_host C)
      (fun q => q = xr_anchor C true ∨ q = xr_anchor C false) hstat hrun hend hA
    have hcut' : ∀ t < T₁,
        ((xr_host C).runFrom (xr_cycle C z false false [] [] [] (fun _ => 0)) t).state ≠
          some (xr_anchor C true) ∧
        ((xr_host C).runFrom (xr_cycle C z false false [] [] [] (fun _ => 0)) t).state ≠
          some (xr_anchor C false) :=
      fun t ht => ⟨fun h => hcut t ht _ h (Or.inl rfl), fun h => hcut t ht _ h (Or.inr rfl)⟩
    have hseam := seamCompTM₂_run_ofCfg (xr_host C) (xr_anchor C true) (xr_anchor C false) he
      (xr_answerTM (N.k + 2 + 2) true) xr_St.start (xr_answerTM (N.k + 2 + 2) false) xr_St.start
      hrun₁ hcut'
    have hcomp : (xr_E C).ComputesInTime z [b] (T₁ + 1 + 1) := by
      rw [FinTM.computesInTime_iff, hE]
      cases b
      · rw [hseam.2 hend 1]
        exact xr_answer_tail false _ _ hend rfl Sum.inr
      · rw [hseam.1 hend 1]
        obtain ⟨h1, h2⟩ := xr_answer_tail true _ _ hend rfl
          (Sum.inr : xr_St → (Σ i, xr_PhSt C i) ⊕ xr_St)
        exact ⟨by rw [Cfg.mapState_state, h1]; rfl, by rw [Cfg.mapState_output, h2]⟩
    exact hcomp.mono (by omega)
  exact ⟨fun hacc => key true (decide_eq_true (hiff.mpr hacc)),
    fun hrej => key false (decide_eq_false fun h => hrej (hiff.mp h))⟩

/-- **The exponential decider from the universal NDTM**, `BF := E(UN)`: if `UN` is a timed
universal NDTM for the scheme `c` (the statement of `Turing.exists_timed_universal_NDTM`), then
there is a deterministic machine `BF` such that for every code `α` there is a constant `C` with
`BF` outputting `[true]` or `[false]` on `⟨⟨bits t, α⟩, x⟩`, according to whether the coded
machine accepts `x` within `t`, within `C·2^{C·(t + 1)}` steps (the statement of
`Turing.exists_ndAcceptsWithin_decider`). [AB09, §3.2, proof of Theorem 3.2, step 2]

**Proof sketch.** `BF` is the exhaustive replay of `UN`
(`Turing.FinNDTM.exists_exhaustiveDecider`) with constant `C_E`. Every branch of `UN` halts
within `C_α·(t + 1)`, so `E` decides `UN`'s acceptance within that bound, which is the coded
machine's acceptance within `t`, in time `C_E·2^{C_E·(C_α·(t + 1) + 1)}`; with
`C := C_E·(C_α + 1)` this is at most `C·2^{C·(t + 1)}`. -/
theorem ndAcceptsWithin_decider_of_universal (c : EffectiveNDMachineCode)
    (hUN : ∃ UN : FinNDTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      UN.tm.HaltsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ∧
      (UN.AcceptsWithin (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) ↔
        (c.decode α).toFinNDTM.AcceptsWithin x t)) :
    ∃ BF : FinTM Bool, ∀ α : List Bool, ∃ C : ℕ, ∀ (x : List Bool) (t : ℕ),
      ((c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [true]
          (C * 2 ^ (C * (t + 1)))) ∧
      (¬(c.decode α).toFinNDTM.AcceptsWithin x t →
        BF.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) [false]
          (C * 2 ^ (C * (t + 1)))) := by
  obtain ⟨UN, hU⟩ := hUN
  obtain ⟨E, CE, hE⟩ := FinNDTM.exists_exhaustiveDecider UN
  refine ⟨E, fun α => ?_⟩
  obtain ⟨C, hC⟩ := hU α
  refine ⟨CE * (C + 1), fun x t => ?_⟩
  obtain ⟨hhalt, hiff⟩ := hC x t
  obtain ⟨hacc, hrej⟩ := hE (pairEncode (pairEncode (Nat.bits t) α) x) (C * (t + 1)) hhalt
  have hexp : CE * (C * (t + 1) + 1) ≤ CE * (C + 1) * (t + 1) := by
    have : C * (t + 1) + 1 ≤ (C + 1) * (t + 1) := by rw [Nat.succ_mul]; omega
    calc CE * (C * (t + 1) + 1) ≤ CE * ((C + 1) * (t + 1)) := Nat.mul_le_mul_left CE this
      _ = CE * (C + 1) * (t + 1) := (Nat.mul_assoc _ _ _).symm
  have hbound : CE * 2 ^ (CE * (C * (t + 1) + 1)) ≤
      CE * (C + 1) * 2 ^ (CE * (C + 1) * (t + 1)) := by
    apply Nat.mul_le_mul
    · exact Nat.le_mul_of_pos_right CE (Nat.succ_pos C)
    · exact Nat.pow_le_pow_right (by omega) hexp
  exact ⟨fun h => (hacc (hiff.mpr h)).mono hbound,
    fun h => (hrej (fun h' => h (hiff.mp h'))).mono hbound⟩

end Turing
```

## ===== TCSlib/Complexity/ClassNP/NDNormalForm.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.TuringMachine.NDCodes
import TCSlib.Complexity.TuringMachine.Build.NDHost
import TCSlib.Complexity.TuringMachine.Build.StepBlock
import TCSlib.Complexity.TuringMachine.CfgFacts
import TCSlib.Complexity.TuringMachine.BufferWords
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The linear-overhead coded normal form of an NDTM

[AB09, §3.2] ([BGW70]-style guess-then-verify): every bundled binary nondeterministic machine has a
coded two-work-tape equivalent (`Turing.CodeNDTM`) whose acceptance tracks the original's at linear
time overhead, forward with an explicit constant and backward in unbounded form. The
nondeterministic time hierarchy (`TCSlib.Complexity.Diagonalization.NTimeHierarchy`) diagonalizes
over these codes. This module isolates the normal-form statement and its supporting construction.

## Main definitions

No new definitions: the normal form is an existential contract.

## Main results

* `Turing.FinNDTM.exists_codeNDTM_accepts_linear` — the linear-overhead coded normal form.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§3.2.)
* [BGW70] R. Book, S. Greibach, B. Wegbreit, *Time- and tape-bounded Turing
  acceptors and AFLs*, JCSS 4(6), 1970. (Cited through [AB09]; no external text is required.)
-/

namespace Turing

namespace FinNDTM

/-- A finite-state machine with two binary work tapes has a code with identical acceptance.

**Proof sketch.** Relabel the finite state type by its equivalence with a finite ordinal.
Read the initial configuration and the relabeled run through their field equations, and
transfer halting and the exact output word in both directions. -/
private theorem nf_pack {S : Type} [Fintype S] (H : NDTM 2 Bool S) :
    ∃ M : CodeNDTM, ∀ (x : List Bool) (t : ℕ), M.toFinNDTM.AcceptsWithin x t ↔
      ∃ w : List Bool, w.length = t ∧ (H.runWith w (H.initCfg x)).state = none ∧
        (H.runWith w (H.initCfg x)).output = [true] := by
  have hpos : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨H.q₀⟩
  let e : S ≃ Fin (Fintype.card S - 1 + 1) :=
    (Fintype.equivFin S).trans (finCongr (by omega))
  refine ⟨⟨Fintype.card S - 1, H.relabelState e⟩, fun x t => ?_⟩
  rw [FinNDTM.acceptsWithin_iff]
  simp only [CodeNDTM.toFinNDTM_tm, CodeNDTM.toFinNDTM_k, CodeNDTM.toFinNDTM_State]
  have hinit : (H.relabelState e).initCfg x = (H.initCfg x).mapState e := by
    rw [NDTM.initCfg_eq, NDTM.initCfg_eq, NDTM.relabelState_q₀]
    exact (Cfg.mapState_eq_of_fields _ e _
      (by rw [Cfg.init_state, Cfg.init_state]; rfl)
      (by rw [Cfg.init_inputPos, Cfg.init_inputPos])
      (by funext i p; rw [Cfg.init_workTapes, Cfg.init_workTapes])
      (by funext i; rw [Cfg.init_workTapePos, Cfg.init_workTapePos])
      (by rw [Cfg.init_output, Cfg.init_output])).symm
  rw [hinit]
  constructor
  · rintro ⟨w, hw, hh, ho⟩
    refine ⟨w, hw, ?_, ?_⟩
    · rw [NDTM.relabelState_runWith, Cfg.mapState_state] at hh
      exact Option.map_eq_none_iff.mp hh
    · rwa [NDTM.relabelState_runWith, Cfg.mapState_output] at ho
  · rintro ⟨w, hw, hh, ho⟩
    refine ⟨w, hw, ?_, ?_⟩
    · rw [NDTM.relabelState_runWith, Cfg.mapState_state, hh]; rfl
    · rwa [NDTM.relabelState_runWith, Cfg.mapState_output]

/-- The trivial setup: a machine started at its exit meets `Turing.guessCtlRunTM`'s setup
hypotheses at time `0`, on every tape. -/
private theorem nf_setup {SP : Type} (P : MultiTapeTM 2 Bool SP) (z : List Bool) (j : Fin 2) :
    P.runFrom (P.initCfg z) 0 = P.initCfg z ∧ (P.initCfg z).state = some P.q₀ ∧
      (∀ u < 0, (P.runFrom (P.initCfg z) u).state ≠ some P.q₀) ∧
      (∀ p : ℕ, (P.initCfg z).workTapes j ((P.initCfg z).workTapePos j + p) = none) ∧
      (P.initCfg z).workTapes j ((P.initCfg z).workTapePos j - 1) = none := by
  refine ⟨MultiTapeTM.runFrom_zero, ?_, fun u hu => absurd hu (Nat.not_lt_zero u), fun p => ?_, ?_⟩
  · rw [MultiTapeTM.initCfg_eq, Cfg.init_state]
  · rw [MultiTapeTM.initCfg_eq, Cfg.init_workTapes]
  · rw [MultiTapeTM.initCfg_eq, Cfg.init_workTapes]

/-- The display controller records the next position and the last completed record's flag. -/
private def nf_ctlStep (k : ℕ) (q : Fin (2 * k + 4) × Bool) (b : Bool) :
    Fin (2 * k + 4) × Bool :=
  if h : q.1.val = 2 * k + 3 then (0, b)
  else (⟨q.1.val + 1, by have := q.1.isLt; omega⟩, q.2)

/-- The controller stops precisely at a record boundary carrying a true end flag. -/
private def nf_ctlStop (k : ℕ) (q : Fin (2 * k + 4) × Bool) : Bool :=
  decide (q.1.val = 0) && q.2

/-- Starting at a record boundary, the position is the length read modulo the record width.

**Proof sketch.** Induct by appending one bit. At the last position the controller resets;
otherwise it advances by one. These are exactly the two cases of addition modulo the width. -/
private theorem nf_ctl_position (k : ℕ) (s : List Bool) (f : Bool) :
    (s.foldl (nf_ctlStep k) (0, f)).1.val = s.length % (2 * k + 4) := by
  induction s using List.reverseRecOn with
  | nil =>
    simp only [List.foldl_nil, List.length_nil, Nat.zero_mod]
    rfl
  | append_singleton s b ih =>
    simp only [List.foldl_concat, List.length_append, List.length_singleton]
    rw [nf_ctlStep]
    split_ifs with h
    · have hm : s.length % (2 * k + 4) = 2 * k + 3 := by omega
      simp only [Nat.succ_mod_succ_eq_zero_iff.mpr hm, Fin.val_zero]
    · have hp := (s.foldl (nf_ctlStep k) (0, f)).1.isLt
      have hm : s.length % (2 * k + 4) + 1 < 2 * k + 4 := by omega
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < 2 * k + 4 by omega),
        Nat.mod_eq_of_lt hm]
      exact congrArg (fun n => n + 1) ih

/-- A nonempty prefix stops exactly when its length is a whole number of records and its
last bit is true.

**Proof sketch.** Separate the empty prefix and a prefix obtained by appending one bit.
The last position resets to zero and records that bit; every other position is nonzero. -/
private theorem nf_ctl_stop_iff (k : ℕ) (s : List Bool) :
    nf_ctlStop k (s.foldl (nf_ctlStep k) (0, false)) = true ↔
      s ≠ [] ∧ s.length % (2 * k + 4) = 0 ∧ s.getLastD false = true := by
  induction s using List.reverseRecOn with
  | nil => simp [nf_ctlStop]
  | append_singleton s b _ =>
    have hp := nf_ctl_position k (s ++ [b]) false
    rw [List.foldl_concat, nf_ctlStep] at hp ⊢
    split_ifs at hp ⊢ with h
    · have hz : (s ++ [b]).length % (2 * k + 4) = 0 := hp.symm
      have hz' : (s.length + 1) % (2 * k + 4) = 0 := by
        simpa only [List.length_append, List.length_singleton] using hz
      simp [nf_ctlStop, hz']
    · have hn : (s ++ [b]).length % (2 * k + 4) ≠ 0 := by
        intro hz
        have hp' : (s.foldl (nf_ctlStep k) (0, false)).1.val + 1 =
            (s ++ [b]).length % (2 * k + 4) := hp
        omega
      have hn' : (s.length + 1) % (2 * k + 4) ≠ 0 := by
        simpa only [List.length_append, List.length_singleton] using hn
      simp [nf_ctlStop, hn']

/-- A record consists of its choice bit, two bits for each claimed read (input first), and
its end flag. A blank is encoded by `00`, false by `10`, and true by `11`. -/
private def nf_record (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool) (last : Bool)
    (p : Fin (2 * k + 4)) : Bool :=
  if p.val = 0 then b
  else if h : p.val = 2 * k + 3 then last
  else
    let i : Fin (k + 1) := ⟨(p.val - 1) / 2, by have := p.isLt; omega⟩
    if (p.val - 1) % 2 = 0 then (reads i).isSome else (reads i).getD false

/-- The last position of a record is its end flag. -/
private theorem nf_record_last (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) : nf_record k b reads last ⟨2 * k + 3, by omega⟩ = last := by
  rw [nf_record, if_neg (show 2 * k + 3 ≠ 0 by omega), dif_pos rfl]

/-- The first position of a record is its choice bit. -/
private theorem nf_record_choice (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) : nf_record k b reads last 0 = b := by
  rw [nf_record, if_pos (show (0 : Fin (2 * k + 4)).val = 0 from rfl)]

/-- Each claimed read occupies its designated presence bit and value bit.

**Proof sketch.** At the two designated offsets the quotient is the claimed-read index.
The remainder distinguishes its presence bit from its value bit. -/
private theorem nf_record_read (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) (i : Fin (k + 1)) :
    nf_record k b reads last ⟨2 * i.val + 1, by omega⟩ = (reads i).isSome ∧
      nf_record k b reads last ⟨2 * i.val + 2, by omega⟩ = (reads i).getD false := by
  have hi := i.isLt
  constructor
  · have hq : (2 * i.val + 1 - 1) / 2 = i.val := by omega
    have hr : (2 * i.val + 1 - 1) % 2 = 0 := by omega
    rw [nf_record, if_neg (show 2 * i.val + 1 ≠ 0 by omega),
      dif_neg (show 2 * i.val + 1 ≠ 2 * k + 3 by omega), if_pos hr]
    exact congrArg (fun j => (reads j).isSome) (Fin.ext hq)
  · have hq : (2 * i.val + 2 - 1) / 2 = i.val := by omega
    have hr : (2 * i.val + 2 - 1) % 2 ≠ 0 := by omega
    rw [nf_record, if_neg (show 2 * i.val + 2 ≠ 0 by omega),
      dif_neg (show 2 * i.val + 2 ≠ 2 * k + 3 by omega), if_neg hr]
    exact congrArg (fun j => (reads j).getD false) (Fin.ext hq)

/-- The display of a branch records the reads before each step, the step's choice bit, and
an end flag only on the last record. Actions and machine states are not guessed. -/
private def nf_display (N : FinNDTM Bool) (x w : List Bool) : List Bool :=
  List.ofFn fun i : Fin ((2 * N.k + 4) * w.length) =>
    let r : Fin w.length := ⟨i.val / (2 * N.k + 4),
      (Nat.div_lt_iff_lt_mul (by omega)).2 (by simpa only [Nat.mul_comm] using i.isLt)⟩
    let p : Fin (2 * N.k + 4) := ⟨i.val % (2 * N.k + 4), Nat.mod_lt _ (by omega)⟩
    let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
    nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
      (decide (r.val + 1 = w.length)) p

/-- A display has exactly `2k + 4` bits per step. -/
private theorem nf_display_length (N : FinNDTM Bool) (x w : List Bool) :
    (nf_display N x w).length = (2 * N.k + 4) * w.length := by
  simp only [nf_display, List.length_ofFn]

/-- The end bit of the `r`th record of a display is true exactly on its last record.

**Proof sketch.** With the width `W = 2k + 4`, the final cell of record `r` has index
`W(r+1)-1`. Its quotient by `W` is `r` and its remainder is `W-1`, so the record encoder returns
the prescribed end flag. -/
private theorem nf_display_flag (N : FinNDTM Bool) (x w : List Bool) (r : Fin w.length) :
    (nf_display N x w)[(2 * N.k + 4) * (r.val + 1) - 1]? =
      some (decide (r.val + 1 = w.length)) := by
  let W := 2 * N.k + 4
  have hW : 0 < W := by omega
  have hprod : 0 < W * (r.val + 1) := Nat.mul_pos hW (by omega)
  have hi : W * (r.val + 1) - 1 < (nf_display N x w).length := by
    rw [nf_display_length]
    have hle := Nat.mul_le_mul_left W (show r.val + 1 ≤ w.length by omega)
    show W * (r.val + 1) - 1 < W * w.length
    omega
  have hd : (W * (r.val + 1) - 1) / W = r.val := by
    simpa only [Nat.zero_add, Nat.zero_div, Nat.add_sub_cancel] using
      Nat.mul_sub_div 0 W (r.val + 1) hprod
  have hm : (W * (r.val + 1) - 1) % W = 2 * N.k + 3 := by
    have he := Nat.mod_add_div (W * (r.val + 1) - 1) W
    rw [hd] at he
    have hdecomp : W * (r.val + 1) = W * r.val + W := by ring
    rw [hdecomp] at he ⊢
    have he' : W = 2 * N.k + 4 := rfl
    omega
  rw [List.getElem?_eq_getElem hi]
  simp only [nf_display, List.getElem_ofFn]
  have hp : (⟨(W * (r.val + 1) - 1) % W, Nat.mod_lt _ hW⟩ : Fin W) =
      ⟨2 * N.k + 3, by omega⟩ := Fin.ext hm
  rw [hp, nf_record_last]
  exact congrArg (fun a : ℕ => some (decide (a + 1 = w.length))) hd

/-- Every nonempty branch display first stops the controller exactly at its end.

**Proof sketch.** A stopping prefix must end on a record boundary. Its last bit is therefore
one of the display's end flags, which is false before the last record and true there. -/
private theorem nf_display_firstStop (N : FinNDTM Bool) (x w : List Bool) (hw : w ≠ []) :
    (∀ i < (nf_display N x w).length,
      nf_ctlStop N.k (((nf_display N x w).take i).foldl (nf_ctlStep N.k) (0, false)) = false) ∧
      nf_ctlStop N.k ((nf_display N x w).foldl (nf_ctlStep N.k) (0, false)) = true := by
  have hwpos : 0 < w.length := List.length_pos_iff.mpr hw
  have hW : 0 < 2 * N.k + 4 := by omega
  constructor
  · intro i hi
    apply Bool.eq_false_iff.mpr
    intro hs
    obtain ⟨hne, hm, hb⟩ := (nf_ctl_stop_iff N.k _).mp hs
    have hipos : 0 < i := (List.length_pos_iff.mpr hne).trans_eq (List.length_take_of_le hi.le)
    rw [List.length_take_of_le hi.le] at hm
    have he := Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hm)
    have hn : 0 < i / (2 * N.k + 4) := Nat.pos_of_mul_pos_left (hipos.trans_eq he.symm)
    have hlt : i / (2 * N.k + 4) < w.length :=
      Nat.div_lt_of_lt_mul (hi.trans_eq (nf_display_length N x w))
    let r : Fin w.length := ⟨i / (2 * N.k + 4) - 1, by omega⟩
    have hr : r.val + 1 = i / (2 * N.k + 4) := by
      show i / (2 * N.k + 4) - 1 + 1 = i / (2 * N.k + 4)
      omega
    have hflag := nf_display_flag N x w r
    rw [hr, he, decide_eq_false (show ¬i / (2 * N.k + 4) = w.length by omega)] at hflag
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take_of_le hi.le,
      List.getElem?_take_of_lt (by omega), hflag, Option.getD_some] at hb
    exact Bool.noConfusion hb
  · apply (nf_ctl_stop_iff N.k _).mpr
    have hspos : 0 < (nf_display N x w).length := by
      rw [nf_display_length]
      exact Nat.mul_pos hW hwpos
    refine ⟨List.ne_nil_of_length_pos hspos, ?_, ?_⟩
    · rw [nf_display_length, Nat.mul_mod_right]
    · let r : Fin w.length := ⟨w.length - 1, by omega⟩
      have hr : r.val + 1 = w.length := by
        show w.length - 1 + 1 = w.length
        omega
      have hf := nf_display_flag N x w r
      rw [hr, decide_eq_true rfl] at hf
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, nf_display_length,
        hf, Option.getD_some]

/-- A stream that first stops the controller consists of a positive number of complete
records, with false end flags on all but the final record, whose end flag is true.

**Proof sketch.** The stopping criterion makes the total length a positive multiple of the
width. Apply the same criterion to each shorter record boundary: its flag must be false,
since a true flag there would contradict the first-stop hypothesis. -/
private theorem nf_firstStop_records (k : ℕ) (s : List Bool)
    (hlive : ∀ i < s.length, nf_ctlStop k ((s.take i).foldl (nf_ctlStep k) (0, false)) = false)
    (hstop : nf_ctlStop k (s.foldl (nf_ctlStep k) (0, false)) = true) :
    ∃ n : ℕ, 0 < n ∧ s.length = (2 * k + 4) * n ∧
      ∀ r < n, s[(2 * k + 4) * (r + 1) - 1]? = some (decide (r + 1 = n)) := by
  obtain ⟨hsne, hmod, hlast⟩ := (nf_ctl_stop_iff k s).mp hstop
  have hspos := List.length_pos_iff.mpr hsne
  have hW : 0 < 2 * k + 4 := by omega
  let n := s.length / (2 * k + 4)
  have hlen : s.length = (2 * k + 4) * n :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
  have hn : 0 < n := Nat.pos_of_mul_pos_left (hspos.trans_eq hlen)
  refine ⟨n, hn, hlen, ?_⟩
  intro r hr
  let m := (2 * k + 4) * (r + 1)
  have hmpos : 0 < m := Nat.mul_pos hW (by omega)
  have hmle : m ≤ s.length := by
    rw [hlen]
    exact Nat.mul_le_mul_left _ (by omega)
  have hib : m - 1 < s.length := by omega
  have hlasttake : (s.take m).getLastD false = s[m - 1] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.length_take_of_le hmle,
      List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hib, Option.getD_some]
  rw [List.getElem?_eq_getElem hib]
  by_cases he : r + 1 = n
  · have hm : m = s.length := by
      show (2 * k + 4) * (r + 1) = s.length
      rw [he, ← hlen]
    have htake : s.take m = s := by rw [hm, List.take_length]
    rw [htake] at hlasttake
    have hb : s[m - 1] = true := hlasttake.symm.trans hlast
    rw [hb, decide_eq_true he]
  · have hmlt : m < s.length := by
      rw [hlen]
      exact Nat.mul_lt_mul_of_pos_left (by omega) hW
    have hb : s[m - 1] = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hniltake : s.take m ≠ [] :=
        List.ne_nil_of_length_pos (hmpos.trans_eq (List.length_take_of_le hmle).symm)
      have hz : (s.take m).length % (2 * k + 4) = 0 := by
        rw [List.length_take_of_le hmle]
        exact Nat.mul_mod_right _ _
      have hf := (nf_ctl_stop_iff k (s.take m)).mpr
        ⟨hniltake, hz, hlasttake.trans htrue⟩
      rw [hlive m hmlt] at hf
      exact Bool.noConfusion hf
    rw [hb, decide_eq_false he]

/-- Displaying the first `t` steps of a long enough branch uses exactly `(2k + 4)t` bits. -/
private theorem nf_display_prefix_length (N : FinNDTM Bool) (x w : List Bool) (t : ℕ)
    (ht : t ≤ w.length) : (nf_display N x (w.take t)).length = (2 * N.k + 4) * t := by
  rw [nf_display_length, List.length_take_of_le ht]

/-- A record's claimed reads; an absent presence bit decodes to blank regardless of its
value bit. Thus the unused code `01` also decodes to blank. -/
private def nf_decode (k : ℕ) (r : Fin (2 * k + 4) → Option Bool)
    (i : Fin (k + 1)) : Option Bool :=
  if (r ⟨2 * i.val + 1, by omega⟩).getD false then
    some ((r ⟨2 * i.val + 2, by omega⟩).getD false)
  else none

/-- Decoding a displayed record recovers each claimed read. -/
private theorem nf_decode_record (k : ℕ) (b : Bool) (reads : Fin (k + 1) → Option Bool)
    (last : Bool) (i : Fin (k + 1)) :
    nf_decode k (fun p => some (nf_record k b reads last p)) i = reads i := by
  rw [nf_decode, Option.getD_some, Option.getD_some,
    (nf_record_read k b reads last i).1, (nf_record_read k b reads last i).2]
  cases reads i <;> rfl

/-- A false presence bit decodes to blank, including the unused fourth two-bit code. -/
private theorem nf_decode_absent (k : ℕ) (r : Fin (2 * k + 4) → Option Bool)
    (i : Fin (k + 1)) (h : (r ⟨2 * i.val + 1, by omega⟩).getD false = false) :
    nf_decode k r i = none := by
  rw [nf_decode, h]
  rfl

/-- The control check retains the simulated state, output summary, and an irreversible
failure flag. -/
private abbrev nf_Control (N : FinNDTM Bool) := Option N.State × Option Bool × Bool

/-- The sweep's finite control retains a position, a partially filled record, and its
control-check data. The record is a function on a finite type, never an unbounded list. -/
private abbrev nf_SweepState (N : FinNDTM Bool) :=
  (Fin (2 * N.k + 4) × (Fin (2 * N.k + 4) → Option Bool)) × nf_Control N

/-- Completing a record recomputes its action and checks its end flag. A record after
halting sets the failure flag. The summary includes emissions of halting transitions. -/
private def nf_complete (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool)
    (c : nf_Control N) : nf_Control N :=
  match c.1 with
  | none => (none, c.2.1, true)
  | some q =>
    let reads := nf_decode N.k r
    let a := N.tm.tr ((r 0).getD false) q (reads 0) (fun j => reads j.succ)
    (a.state, StepBlock.summaryEmit c.2.1 a.output,
      c.2.2 || decide ((r ⟨2 * N.k + 3, by omega⟩).getD false ≠ a.state.isNone))

/-- The bit fold stores one bit, completing the record exactly at its last position. -/
private def nf_sweepStep (N : FinNDTM Bool) (c : nf_SweepState N) (b : Bool) :
    nf_SweepState N :=
  let r := Function.update c.1.2 c.1.1 (some b)
  if h : c.1.1.val = 2 * N.k + 3 then
    ((0, fun _ => none), nf_complete N r c.2)
  else ((⟨c.1.1.val + 1, by have := c.1.1.isLt; omega⟩, r), c.2)

/-- The control sweep begins at the start state with an empty record and output summary. -/
private def nf_sweepInit (N : FinNDTM Bool) : nf_SweepState N :=
  ((0, fun _ => none), (some N.tm.q₀, none, false))

/-- The control check passes only at a complete record boundary, after halting, with an
accepting output summary and no failure. -/
private def nf_sweepPass (N : FinNDTM Bool) (c : nf_SweepState N) : Bool :=
  decide (c.1.1.val = 0) && c.2.1.isNone && decide (c.2.2.1 = some true) && !c.2.2.2

/-- On an encoded record, the completion rule is precisely the recomputed action and its
summary update; it marks an error exactly when the end flag disagrees with halting. -/
private theorem nf_complete_record (N : FinNDTM Bool) (b : Bool)
    (reads : Fin (N.k + 1) → Option Bool) (last : Bool) (q : N.State)
    (o : Option Bool) (failed : Bool) :
    let a := N.tm.tr b q (reads 0) (fun j => reads j.succ)
    nf_complete N (fun p => some (nf_record N.k b reads last p)) (some q, o, failed) =
      (a.state, StepBlock.summaryEmit o a.output, failed || decide (last ≠ a.state.isNone)) := by
  intro a
  have hd : nf_decode N.k (fun p => some (nf_record N.k b reads last p)) = reads := by
    funext i
    exact nf_decode_record N.k b reads last i
  rw [nf_complete, hd, nf_record_choice, nf_record_last, Option.getD_some, Option.getD_some]

/-- A failed control check remains failed after every subsequent completed record. -/
private theorem nf_complete_failed (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool)
    (q : Option N.State) (o : Option Bool) :
    (nf_complete N r (q, o, true)).2.2 = true := by
  cases q <;> simp only [nf_complete, Bool.true_or]

/-- Once the output summary is rejecting, later completed records cannot repair it. -/
private theorem nf_complete_other (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool)
    (q : Option N.State) (failed : Bool) :
    (nf_complete N r (q, some false, failed)).2.1 = some false := by
  cases q <;> simp only [nf_complete, StepBlock.summaryEmit_other]

/-- Before the last bit, scanning a record stores exactly its prefix and leaves the
simulated state, summary, and failure flag unchanged.

**Proof sketch.** Induct on the prefix length. Before the last position the fold performs
only one array update. At its index the newly stored bit extends the prefix; at other
indices the old prefix description remains valid. -/
private theorem nf_sweep_prefix (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Bool)
    (c : nf_Control N) (n : ℕ) (hn : n < 2 * N.k + 4) :
    (List.ofFn fun i : Fin n => r ⟨i.val, by omega⟩).foldl (nf_sweepStep N)
        ((0, fun _ => none), c) =
      ((⟨n, hn⟩, fun j => if j.val < n then some (r j) else none), c) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.foldl_nil]
    congr 2
  | succ n ih =>
    rw [List.ofFn_succ_last, List.foldl_concat]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih (by omega)]
    simp only [nf_sweepStep]
    rw [dif_neg (show n ≠ 2 * N.k + 3 by omega)]
    congr 2
    funext j
    by_cases he : j = (⟨n, by omega⟩ : Fin (2 * N.k + 4))
    · subst j
      rw [Function.update_self, if_pos (show n < n + 1 by omega)]
    · rw [Function.update_of_ne he]
      have hne : j.val ≠ n := fun h => he (Fin.ext h)
      by_cases hlt : j.val < n
      · rw [if_pos hlt, if_pos (by omega)]
      · rw [if_neg hlt, if_neg (by omega)]

/-- Storing a record's last bit completes the parser's prefix array: the array that holds the
first `2k + 3` bits, updated at the last position, holds every bit. -/
private theorem nf_update_last (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Bool) :
    Function.update
      (fun j : Fin (2 * N.k + 4) => if j.val < 2 * N.k + 3 then some (r j) else none)
      ⟨2 * N.k + 3, by omega⟩ (some (r ⟨2 * N.k + 3, by omega⟩)) =
        fun j => some (r j) := by
  funext j
  by_cases he : j = (⟨2 * N.k + 3, by omega⟩ : Fin (2 * N.k + 4))
  · subst j
    rw [Function.update_self]
  · rw [Function.update_of_ne he, if_pos (by
      have hj := j.isLt
      have hne : j.val ≠ 2 * N.k + 3 := fun h => he (Fin.ext h)
      omega)]

/-- Scanning one whole record resets the parser and applies exactly one completion rule.

**Proof sketch.** Apply the prefix law to all but the last bit. The final array update
fills the only missing entry; the last-position branch resets the parser and checks the
completed record. -/
private theorem nf_sweep_record (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Bool)
    (c : nf_Control N) :
    (List.ofFn r).foldl (nf_sweepStep N) ((0, fun _ => none), c) =
      ((0, fun _ => none), nf_complete N (fun p => some (r p)) c) := by
  rw [List.ofFn_succ_last, List.foldl_concat]
  have hf : (fun i : Fin (2 * N.k + 3) => r i.castSucc) =
      fun i => r ⟨i.val, by omega⟩ := by
    funext i
    rfl
  rw [hf, nf_sweep_prefix N r c (2 * N.k + 3) (by omega)]
  simp only [nf_sweepStep]
  rw [dite_true]
  rw [show (Fin.last (2 * N.k + 3) : Fin (2 * N.k + 4)) =
    ⟨2 * N.k + 3, by omega⟩ from rfl, nf_update_last N r]

/-- A completed live record updates the output summary exactly as its optional emission
updates the output word, including an emission on a halting transition. -/
private theorem nf_complete_output (N : FinNDTM Bool) (b : Bool)
    (reads : Fin (N.k + 1) → Option Bool) (last : Bool) (q : N.State)
    (o : List Bool) (failed : Bool) :
    let a := N.tm.tr b q (reads 0) (fun j => reads j.succ)
    (nf_complete N (fun p => some (nf_record N.k b reads last p))
      (some q, StepBlock.outputSummary o, failed)).2.1 =
        StepBlock.outputSummary (o ++ a.output.toList) := by
  intro a
  rw [nf_complete_record, StepBlock.outputSummary_append]

/-- The sweep's accepting summary means that the simulated output is exactly `[true]`. -/
private theorem nf_sweepPass_output (N : FinNDTM Bool) (c : nf_SweepState N) (o : List Bool)
    (ho : c.2.2.1 = StepBlock.outputSummary o) (hp : nf_sweepPass N c = true) :
    o = [true] := by
  rw [nf_sweepPass, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hp
  exact (StepBlock.outputSummary_true o).mp (ho.symm.trans (of_decide_eq_true hp.1.2))

/-- **The control sweep is the fold instance of `Turing.scanTM`.** From the stream start with
the scan's forward state, the scan on tape `0` reaches the completed bit fold at exactly
`2|s| + 2`, not at any `done` before, with every tape, head, the input head and the output as at
the start: the head of tape `0` is back at cell `0` with no separate rewind.

**Proof sketch.** Apply the framed scan contract with the fold and identity backward pass.
The scan-result equation identifies the final fold and unchanged word; the configuration
field equations show that every other tape, position and output field is preserved. -/
private theorem nf_sweep_run (N : FinNDTM Bool) (x s : List Bool) :
    (scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)).runFrom
        (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s)
        (2 * s.length + 2) =
      streamStartCfg x 0 (ScanPhase.done (s.foldl (nf_sweepStep N) (nf_sweepInit N))) s ∧
      ∀ t < 2 * s.length + 2, ∀ a,
        ((scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)).runFrom
          (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s) t).state ≠
            some (ScanPhase.done a) := by
  have hw : ∀ p : ℤ, -1 ≤ p → p ≤ (s.length : ℤ) →
      (streamStartCfg x (0 : Fin 2) (ScanPhase.fwd (nf_sweepInit N)) s).workTapes 0
        ((streamStartCfg x (0 : Fin 2) (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos 0 + p) =
          FinTM.bufferTape s p := by
    intro p _ _
    rw [streamStartCfg_workTapes, streamStartCfg_workTapePos, if_pos rfl, zero_add]
  obtain ⟨h1, h2, -⟩ := scanTM_run_ofCfg (k := 2) (0 : Fin 2)
    (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N) s
    (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s) (streamStartCfg_state _ _ _ _) hw
  refine ⟨?_, h2⟩
  rw [h1, scanResult_fold]
  apply Cfg.ext
  · rw [streamStartCfg_state]
  · rw [streamStartCfg_inputPos, streamStartCfg_inputPos]
  · funext j q
    show (if j = 0 ∧ (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos j ≤ q ∧
        q < (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos j + (s.length : ℤ)
        then FinTM.bufferTape s
          (q - (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapePos j)
        else (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s).workTapes j q) = _
    rw [streamStartCfg_workTapes, streamStartCfg_workTapes, streamStartCfg_workTapePos]
    split_ifs with h hj <;> simp_all
  · funext j
    rw [streamStartCfg_workTapePos, streamStartCfg_workTapePos]
  · rw [streamStartCfg_output, streamStartCfg_output]

/-- A sequence of whole records is checked by folding their completion rules, with the
bit parser reset between records. -/
private theorem nf_sweep_records (N : FinNDTM Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) (c : nf_Control N) :
    (rs.flatMap (fun r => List.ofFn r)).foldl (nf_sweepStep N) ((0, fun _ => none), c) =
      ((0, fun _ => none), rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) c) := by
  induction rs generalizing c with
  | nil => simp only [List.flatMap_nil, List.foldl_nil]
  | cons r rs ih =>
    rw [List.flatMap_cons, List.foldl_append, nf_sweep_record, ih, List.foldl_cons]

/-- A displayed branch is the concatenation of its fixed-width records.

**Proof sketch.** Split the finite index into its record index and offset by the product
formula for `List.ofFn`. Division and remainder by the width recover those two indices. -/
private theorem nf_display_records (N : FinNDTM Bool) (x w : List Bool) :
    nf_display N x w = (List.ofFn fun r : Fin w.length =>
      let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
      nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
        (decide (r.val + 1 = w.length))).flatMap (fun r => List.ofFn r) := by
  rw [nf_display, List.ofFn_mul', List.flatMap_def, List.map_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext r
  apply congrArg List.ofFn
  funext p
  simp only [Nat.mul_add_div (show 0 < 2 * N.k + 4 by omega),
    Nat.div_eq_of_lt p.isLt, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt p.isLt]

/-- The sweep's final control on a display is the fold of that display's recomputed
records, starting at the original machine's start state and empty output. -/
private theorem nf_sweep_display (N : FinNDTM Bool) (x w : List Bool) :
    (nf_display N x w).foldl (nf_sweepStep N) (nf_sweepInit N) =
      ((0, fun _ => none), (List.ofFn fun r : Fin w.length =>
        let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
        nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
          (decide (r.val + 1 = w.length))).foldl
            (fun d r => nf_complete N (fun p => some (r p)) d)
            (some N.tm.q₀, none, false)) := by
  rw [nf_display_records, nf_sweepInit, nf_sweep_records]

/-- For a live configuration, completing its genuine record gives the next state and
output summary, and compares the flag with the actual next configuration's halting status. -/
private theorem nf_complete_step (N : FinNDTM Bool) (x : List Bool)
    (c : Cfg N.k Bool N.State x) (b last failed : Bool) (hlive : c.state ≠ none) :
    nf_complete N
        (fun p => some (nf_record N.k b (Fin.cases c.inputSymbol c.workTapeSymbols) last p))
        (c.state, StepBlock.outputSummary c.output, failed) =
      ((N.tm.stepWith b c).state, StepBlock.outputSummary (N.tm.stepWith b c).output,
        failed || decide (last ≠ (N.tm.stepWith b c).state.isNone)) := by
  cases hq : c.state with
  | none => exact False.elim (hlive hq)
  | some q =>
    rw [nf_complete_record, NDTM.stepWith_of_some hq, Action.apply_state,
      Action.apply_output, StepBlock.outputSummary_append]
    simp only [Fin.cases_zero, Fin.cases_succ]

/-- On every prefix of a first-halting display, the control fold agrees with the genuine
state and output and has no failed end-flag check.

**Proof sketch.** Induct on the record count. The empty prefix is the initial configuration.
For a further record, the old configuration is live by hypothesis. Its genuine record
therefore gives exactly the next configuration's state and output summary. The next state
is halted exactly at the full word, which is exactly when the displayed end flag is set. -/
private theorem nf_sweep_control_prefix (N : FinNDTM Bool) (x w : List Bool)
    (hlive : ∀ r < w.length, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state ≠ none)
    (hhalt : (N.tm.runWith w (N.tm.initCfg x)).state = none) (n : ℕ) (hn : n ≤ w.length) :
    (List.ofFn fun r : Fin n =>
      let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
      nf_record N.k (w[r.val]'(by omega)) (Fin.cases c.inputSymbol c.workTapeSymbols)
        (decide (r.val + 1 = w.length))).foldl
          (fun d r => nf_complete N (fun p => some (r p)) d) (some N.tm.q₀, none, false) =
      ((N.tm.runWith (w.take n) (N.tm.initCfg x)).state,
        StepBlock.outputSummary (N.tm.runWith (w.take n) (N.tm.initCfg x)).output, false) := by
  induction n with
  | zero =>
    simp only [List.ofFn_zero, List.foldl_nil, List.take_zero, NDTM.runWith_nil,
      NDTM.initCfg_eq, Cfg.init_state, Cfg.init_output, StepBlock.outputSummary_nil]
  | succ n ih =>
    have hlt : n < w.length := by omega
    have hnext : N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x) =
        N.tm.stepWith w[n] (N.tm.runWith (w.take n) (N.tm.initCfg x)) := by
      rw [List.take_succ_eq_append_getElem hlt, NDTM.runWith_append,
        NDTM.runWith_cons, NDTM.runWith_nil]
    have hflag : decide (n + 1 = w.length) =
        (N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state.isNone := by
      by_cases he : n + 1 = w.length
      · rw [he, decide_eq_true rfl, List.take_length, hhalt]
        rfl
      · rw [decide_eq_false he]
        have hnot := hlive (n + 1) (by omega)
        cases hs : (N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state with
        | none => exact False.elim (hnot hs)
        | some q => rfl
    rw [List.ofFn_succ_last, List.foldl_concat]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [ih (by omega), nf_complete_step N x _ _ _ _ (hlive n hlt), ← hnext, hflag]
    have hfalse : (decide ((N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state.isNone ≠
        (N.tm.runWith (w.take (n + 1)) (N.tm.initCfg x)).state.isNone) : Bool) = false :=
      decide_eq_false (fun h => h rfl)
    rw [hfalse, Bool.false_or]

/-- The control sweep passes the display of a branch that first halts at its end with output
exactly `[true]`.

**Proof sketch.** The display decomposition and record-fold law identify the bit fold with
the control fold. The prefix theorem at the whole word gives a halted state, the genuine
output summary, and no failure. The output-summary characterization then gives the pass bit. -/
private theorem nf_sweep_display_pass (N : FinNDTM Bool) (x w : List Bool)
    (hlive : ∀ r < w.length, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state ≠ none)
    (hhalt : (N.tm.runWith w (N.tm.initCfg x)).state = none)
    (hout : (N.tm.runWith w (N.tm.initCfg x)).output = [true]) :
    nf_sweepPass N ((nf_display N x w).foldl (nf_sweepStep N) (nf_sweepInit N)) = true := by
  rw [nf_sweep_display]
  have hc := nf_sweep_control_prefix N x w hlive hhalt w.length (Nat.le_refl _)
  simp only [List.take_length] at hc
  rw [hc, nf_sweepPass, hhalt]
  have ho := (StepBlock.outputSummary_true _).mpr hout
  rw [ho]
  rfl

section

attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg Turing.NDTM.initCfg

/-! ### The verifier's layout

The verifier is a deterministic two-tape machine composed by `Turing.phaseHostTM`. It runs the
control sweep (a fold by `Turing.scanTM` over the stream on tape `0`), then one replay per
replayed tape (the input first, then each work tape on tape `1`), each followed by the return of
tape `0` (`Turing.skipTM`, `Turing.skipBackTM`) and, for a work tape, the clear of tape `1`
(`Turing.skipTM`, `Turing.skipBackTM`, `Turing.clearTM`), and ends in a stationary verdict
park. It is silent: no phase emits output. -/

/-- The verifier's phases for `k` work tapes. -/
private inductive nf_Ph (k : ℕ) where
  /-- the control sweep, a scan fold over the stream on tape `0` -/
  | ctl
  /-- the replay of tape `j` (`none`: the input; `some j`: work tape `j`, on tape `1`) -/
  | rep (j : Option (Fin k))
  /-- the return of tape `0`, first step: from the blank after the stream, one cell right -/
  | aFwd (j : Option (Fin k))
  /-- the return of tape `0`, second step: back to cell `0` -/
  | aBack (j : Option (Fin k))
  /-- the clear of tape `1`, first step: to one past the visited region's right blank -/
  | bFwd (j : Fin k)
  /-- the clear of tape `1`, second step: back to the visited region's first cell -/
  | bBack (j : Fin k)
  /-- the clear of tape `1`, third step: blank the visited region -/
  | bClr (j : Fin k)
  /-- the verdict park -/
  | park
  deriving DecidableEq, Fintype

/-- The states of each phase, over the replay leaf's state type `SL`. -/
private def nf_St (N : FinNDTM Bool) (SL : Type) : nf_Ph N.k → Type
  | .ctl => ScanPhase (nf_SweepState N)
  | .rep _ => SL
  | .aFwd _ => SeekPhase
  | .aBack _ => SeekPhase
  | .bFwd _ => SeekPhase
  | .bBack _ => SeekPhase
  | .bClr _ => SweepPhase
  | .park => Bool

/-- Decidable equality of each phase's states, named: default synthesis does not reach
`ScanPhase (nf_SweepState N)` at the default instance size. -/
private instance nf_stDecEq (N : FinNDTM Bool) (SL : Type) [DecidableEq SL] :
    (i : nf_Ph N.k) → DecidableEq (nf_St N SL i)
  | .ctl => @instDecidableEqScanPhase _ inferInstance
  | .rep _ => (inferInstance : DecidableEq SL)
  | .aFwd _ => (inferInstance : DecidableEq SeekPhase)
  | .aBack _ => (inferInstance : DecidableEq SeekPhase)
  | .bFwd _ => (inferInstance : DecidableEq SeekPhase)
  | .bBack _ => (inferInstance : DecidableEq SeekPhase)
  | .bClr _ => (inferInstance : DecidableEq SweepPhase)
  | .park => (inferInstance : DecidableEq Bool)

/-- Finiteness of each phase's states, named as `nf_stDecEq` is. -/
private instance nf_stFintype (N : FinNDTM Bool) (SL : Type) [Fintype SL] :
    (i : nf_Ph N.k) → Fintype (nf_St N SL i)
  | .ctl => @instFintypeScanPhase _ inferInstance
  | .rep _ => (inferInstance : Fintype SL)
  | .aFwd _ => (inferInstance : Fintype SeekPhase)
  | .aBack _ => (inferInstance : Fintype SeekPhase)
  | .bFwd _ => (inferInstance : Fintype SeekPhase)
  | .bBack _ => (inferInstance : Fintype SeekPhase)
  | .bClr _ => (inferInstance : Fintype SweepPhase)
  | .park => (inferInstance : Fintype Bool)

/-- The verdict park: it stays at its state and moves nothing. -/
private def nf_park : MultiTapeTM 2 Bool Bool :=
  ⟨true, fun q _ _ => ⟨0, fun _ => (none, 0), none, some q⟩⟩

/-- The phase machines, over a replay leaf `L` per replayed tape. -/
private def nf_M (N : FinNDTM Bool) {SL : Type} (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) :
    (i : nf_Ph N.k) → MultiTapeTM 2 Bool (nf_St N SL i)
  | .ctl => scanTM 2 0 (scanFold (nf_sweepStep N)) scanKeep (nf_sweepInit N)
  | .rep j => L j
  | .aFwd _ => skipTM 2 0
  | .aBack _ => skipBackTM 2 0
  | .bFwd _ => skipTM 2 1
  | .bBack _ => skipBackTM 2 1
  | .bClr _ => clearTM 2 1
  | .park => nf_park

/-- After tape `j`'s phases: the next work tape's replay, or the passing verdict. -/
private def nf_after (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) : Option (Fin N.k) → Σ i, nf_St N SL i
  | none => if h : 0 < N.k then ⟨.rep (some ⟨0, h⟩), (L (some ⟨0, h⟩)).q₀⟩ else ⟨.park, true⟩
  | some j =>
    if h : j.val + 1 < N.k then ⟨.rep (some ⟨j.val + 1, h⟩), (L (some ⟨j.val + 1, h⟩)).q₀⟩
    else ⟨.park, true⟩

/-- The redirect table: each phase's exit to the next phase's start, a failure to the rejecting
park. `exit` reads the replay leaf's verdict states (`some true` passed, `some false` failed). -/
private def nf_red (N : FinNDTM Bool) {SL : Type} (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL)
    (exit : SL → Option Bool) : (i : nf_Ph N.k) → nf_St N SL i → Option (Σ i, nf_St N SL i)
  | .ctl, .done a =>
    some (if nf_sweepPass N a then ⟨.rep none, (L none).q₀⟩ else ⟨.park, false⟩)
  | .ctl, .fwd _ => none
  | .ctl, .bwd _ => none
  | .rep j, q =>
    match exit q with
    | some true => some ⟨.aFwd j, .run⟩
    | some false => some ⟨.park, false⟩
    | none => none
  | .aFwd j, .done => some ⟨.aBack j, .run⟩
  | .aFwd _, .run => none
  | .aFwd _, .gap => none
  | .aFwd _, .back => none
  | .aBack none, .done => some (nf_after N L none)
  | .aBack (some j), .done => some ⟨.bFwd j, .run⟩
  | .aBack _, .run => none
  | .aBack _, .gap => none
  | .aBack _, .back => none
  | .bFwd j, .done => some ⟨.bBack j, .run⟩
  | .bFwd _, .run => none
  | .bFwd _, .gap => none
  | .bFwd _, .back => none
  | .bBack j, .done => some ⟨.bClr j, .sweep⟩
  | .bBack _, .run => none
  | .bBack _, .gap => none
  | .bBack _, .back => none
  | .bClr j, .done => some (nf_after N L (some j))
  | .bClr _, .sweep => none
  | .bClr _, .rewind => none
  | .park, _ => none

/-- The verifier: the phase host over the phases, entered at the control sweep. -/
private def nf_V (N : FinNDTM Bool) {SL : Type} (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL)
    (exit : SL → Option Bool) : MultiTapeTM 2 Bool (Σ i, nf_St N SL i) :=
  phaseHostTM (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ (nf_red N L exit)

/-! ### The replay leaf

One two-tape machine, parameterized by the replayed tape (`none` the input, `some j` work tape
`j`). It reads tape `0` one cell per step with the control sweep's own record parser and control
(`nf_sweepStep`), so its simulated state is the control sweep's, and at each completed record
recomputes the action of `N`'s table on the record's decoded claims (`nf_decode`). The input
instance compares the decoded input claim with the cell under the native input head and performs
the recomputed input move. A work-tape instance keeps the replayed tape on tape `1` as two-bit
blocks, two nonblank bits per visited cell (`nf_record`'s code) and two blanks per unvisited
cell: at each record it checks the decoded claim against the block under its head, rewrites the
block with the cell's new content, and moves two cells per simulated move, except after the
end-flagged record. -/

/-- The replay leaf's states. -/
private inductive nf_LeafSt (N : FinNDTM Bool) : Type
  /-- reading the stream on tape `0`, with the control sweep's parser and control -/
  | read (σ : nf_SweepState N)
  /-- at the first cell of the replayed cell's block on tape `1`, with the record's claim, the
  cell's new content, the simulated move and the end flag -/
  | blk₁ (σ : nf_SweepState N) (claim new : Option Bool) (mv : SignType) (last : Bool)
  /-- at the block's second cell, with its first cell's old content `β` -/
  | blk₂ (σ : nf_SweepState N) (claim new : Option Bool) (mv : SignType) (last : Bool)
      (β : Option Bool)
  /-- the first of the two head adjustments on tape `1` after a block -/
  | adj₁ (σ : nf_SweepState N) (mv : SignType)
  /-- the second head adjustment -/
  | adj₂ (σ : nf_SweepState N) (mv : SignType)
  /-- the passing exit -/
  | pass
  /-- the rejecting exit -/
  | rej

/-- The replay leaf's states as a sum of finite types, for its instances. -/
private def nf_leafEquiv (N : FinNDTM Bool) : nf_LeafSt N ≃
    nf_SweepState N ⊕ (nf_SweepState N × Option Bool × Option Bool × SignType × Bool) ⊕
      (nf_SweepState N × Option Bool × Option Bool × SignType × Bool × Option Bool) ⊕
      (nf_SweepState N × SignType) ⊕ (nf_SweepState N × SignType) ⊕ Bool where
  toFun
    | .read σ => .inl σ
    | .blk₁ σ c n m l => .inr (.inl (σ, c, n, m, l))
    | .blk₂ σ c n m l β => .inr (.inr (.inl (σ, c, n, m, l, β)))
    | .adj₁ σ m => .inr (.inr (.inr (.inl (σ, m))))
    | .adj₂ σ m => .inr (.inr (.inr (.inr (.inl (σ, m)))))
    | .pass => .inr (.inr (.inr (.inr (.inr true))))
    | .rej => .inr (.inr (.inr (.inr (.inr false))))
  invFun
    | .inl σ => .read σ
    | .inr (.inl (σ, c, n, m, l)) => .blk₁ σ c n m l
    | .inr (.inr (.inl (σ, c, n, m, l, β))) => .blk₂ σ c n m l β
    | .inr (.inr (.inr (.inl (σ, m)))) => .adj₁ σ m
    | .inr (.inr (.inr (.inr (.inl (σ, m))))) => .adj₂ σ m
    | .inr (.inr (.inr (.inr (.inr b)))) => if b then .pass else .rej
  left_inv s := by cases s <;> rfl
  right_inv s := by
    rcases s with σ | ⟨σ, c, n, m, l⟩ | ⟨σ, c, n, m, l, β⟩ | ⟨σ, m⟩ | ⟨σ, m⟩ | b
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases b <;> rfl

/-- Decidable equality of the replay leaf's states. -/
private instance nf_leafStDecEq (N : FinNDTM Bool) : DecidableEq (nf_LeafSt N) :=
  letI : DecidableEq (nf_SweepState N) := inferInstance
  letI : DecidableEq (Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : DecidableEq (nf_SweepState N × Option Bool × Option Bool × SignType × Bool) :=
    inferInstance
  letI : DecidableEq
      (nf_SweepState N × Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : DecidableEq (nf_SweepState N × SignType) := inferInstance
  (nf_leafEquiv N).decidableEq

/-- Finiteness of the replay leaf's states. -/
private instance nf_leafStFintype (N : FinNDTM Bool) : Fintype (nf_LeafSt N) :=
  letI : Fintype (nf_SweepState N) := inferInstance
  letI : Fintype (Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : Fintype (nf_SweepState N × Option Bool × Option Bool × SignType × Bool) :=
    inferInstance
  letI : Fintype
      (nf_SweepState N × Option Bool × Option Bool × SignType × Bool × Option Bool) :=
    inferInstance
  letI : Fintype (nf_SweepState N × SignType) := inferInstance
  Fintype.ofEquiv _ (nf_leafEquiv N).symm

/-- The action of `N`'s table on a completed record at a live simulated state, read through the
record's decoded claims: the action `nf_complete` recomputes. -/
private def nf_act (N : FinNDTM Bool) (r : Fin (2 * N.k + 4) → Option Bool) (q : N.State) :
    Action N.k Bool N.State :=
  N.tm.tr ((r 0).getD false) q (nf_decode N.k r 0) (fun j => nf_decode N.k r j.succ)

/-- A block of tape `1` decodes as `nf_decode` reads a claim: a false or blank first cell is a
blank cell. -/
private def nf_blockDecode (β₁ β₂ : Option Bool) : Option Bool :=
  if β₁.getD false then some (β₂.getD false) else none

/-- **The replay leaf** for the replayed tape `j` (`none` the input, `some j` work tape `j`).
It is a hand-built machine because no public row reads fixed-width records off one tape while
checking them against another: `Turing.scanTM` reads one tape, and the record reader of
`Turing.StepBlock` reads records on `k + 2` tapes. -/
private def nf_leaf (N : FinNDTM Bool) (j : Option (Fin N.k)) :
    MultiTapeTM 2 Bool (nf_LeafSt N) where
  q₀ := .read (nf_sweepInit N)
  tr := fun st inp w =>
    match st with
    | .read σ =>
      if σ.1.1.val = 2 * N.k + 3 then
        match σ.2.1, j with
        | none, _ => tapeAction 0 0 none 0 .rej
        | some q, none =>
          if nf_decode N.k (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) 0 = inp then
            tapeAction 0
              (nf_act N (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) q).inputTape none 1
              (if (w 0).getD false then .pass else .read (nf_sweepStep N σ ((w 0).getD false)))
          else tapeAction 0 0 none 0 .rej
        | some q, some t =>
          tapeAction 0 0 none 1 (.blk₁ (nf_sweepStep N σ ((w 0).getD false))
            (nf_decode N.k (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) t.succ)
            (((nf_act N (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) q).workTapes
              t).1.getD
              (nf_decode N.k (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) t.succ))
            ((nf_act N (Function.update σ.1.2 σ.1.1 (some ((w 0).getD false))) q).workTapes t).2
            ((w 0).getD false))
      else tapeAction 0 0 none 1 (.read (nf_sweepStep N σ ((w 0).getD false)))
    | .blk₁ σ c n m l => tapeAction 1 0 (some (some n.isSome)) 1 (.blk₂ σ c n m l (w 1))
    | .blk₂ σ c n m l β =>
      if nf_blockDecode β (w 1) = c then
        tapeAction 1 0 (some (some (n.getD false))) (if l then 0 else if m = 1 then 1 else -1)
          (if l then .pass else .adj₁ σ m)
      else tapeAction 1 0 none 0 .rej
    | .adj₁ σ m => tapeAction 1 0 none (if m = -1 then -1 else 0) (.adj₂ σ m)
    | .adj₂ σ m => tapeAction 1 0 none (if m = -1 then -1 else 0) (.read σ)
    | .pass => tapeAction 0 0 none 0 .pass
    | .rej => tapeAction 0 0 none 0 .rej

/-- The replay leaf's verdict states: `pass` passed, `rej` failed, every other state live. -/
private def nf_leafExit (N : FinNDTM Bool) : nf_LeafSt N → Option Bool
  | .pass => some true
  | .rej => some false
  | _ => none

-- the verifier's state type is finite with decidable equality, by the named instances
example (N : FinNDTM Bool) : DecidableEq (Σ i, nf_St N (nf_LeafSt N) i) := inferInstance
example (N : FinNDTM Bool) : Fintype (Σ i, nf_St N (nf_LeafSt N) i) := inferInstance

/-! ### Chaining the verifier's phases -/

/-- A configuration whose state is redirected to `⟨i, q⟩` is the tagged configuration of phase
`i` at `q`. -/
private theorem nf_retag {N : FinNDTM Bool} {SL S : Type} {x : List Bool}
    (c : Cfg 2 Bool S x) (i : nf_Ph N.k) (q : nf_St N SL i) (hc : c.state.isSome) :
    c.mapState (fun _ => (⟨i, q⟩ : Σ i, nf_St N SL i)) =
      ({ state := some q, inputPos := c.inputPos, workTapes := c.workTapes,
          workTapePos := c.workTapePos, output := c.output } : Cfg 2 Bool (nf_St N SL i) x).mapState
        (Sigma.mk i) :=
  Cfg.mapState_const_eq_mapState_sigma c _ hc rfl rfl rfl rfl rfl

/-- A configuration tagged by a phase other than the park is at no verdict. -/
private theorem nf_tagged_ne_park {N : FinNDTM Bool} {SL : Type} {x : List Bool}
    {i : nf_Ph N.k} (hi : i ≠ .park) (c : Cfg 2 Bool (nf_St N SL i) x) (b : Bool) :
    (c.mapState (Sigma.mk i)).state ≠ some ⟨.park, b⟩ :=
  Cfg.mapState_sigma_state_ne i _ hi c

/-- The redirect after the return of tape `0`: the next tape's replay or the verdict after the
input, the clear of tape `1` after a work tape. -/
private def nf_aNext (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) : Option (Fin N.k) → Σ i, nf_St N SL i
  | none => nf_after N L none
  | some j => ⟨.bFwd j, .run⟩

/-- **The return of tape `0` after a replay.** From the head of tape `0` on the blank after the
stream `s` (tape `0` holding `s` from cell `0`), the verifier's phases `aFwd j` (`Turing.skipTM`
at `w := []`) and `aBack j` (`Turing.skipBackTM` at `u := s`) bring that head to cell `0` and
redirect to `nf_aNext N L j`, in `|s| + 6` steps, with the tapes, the head of tape `1`, the input
head and the output unchanged, and at no verdict on the way.

**Proof sketch.** Chain the two framed seek runs through the phase lemma of the phase host,
reading the redirected configuration as the second phase's start. Inside each phase the host's
run is the phase's run tagged by that phase, which is not the park. -/
private theorem nf_aReturn (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) (exit : SL → Option Bool) {x : List Bool}
    (j : Option (Fin N.k)) (s : List Bool) (c : Cfg 2 Bool SeekPhase x)
    (hst : c.state = some .run) (hpos : c.workTapePos 0 = s.length)
    (htape : ∀ p, c.workTapes 0 p = FinTM.bufferTape s p) :
    ∃ c₃ : Cfg 2 Bool SeekPhase x,
      (nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.aFwd j)) x).mapState (Sigma.mk (nf_Ph.aFwd j)))
          (s.length + 6) = c₃.mapState (fun _ => nf_aNext N L j) ∧
        c₃.state.isSome ∧
        c₃.workTapePos 0 = 0 ∧ c₃.workTapePos 1 = c.workTapePos 1 ∧ c₃.workTapes = c.workTapes ∧
        c₃.inputPos = c.inputPos ∧ c₃.output = c.output ∧
        ∀ u < s.length + 6, ∀ b, ((nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.aFwd j)) x).mapState (Sigma.mk (nf_Ph.aFwd j)))
            u).state ≠ some ⟨.park, b⟩ := by
  -- phase `aFwd j`: one step right, over the blank
  have hw : ∀ p : ℤ, 0 ≤ p → p ≤ (([] : List Bool).length : ℤ) →
      c.workTapes 0 (c.workTapePos 0 + p) = FinTM.bufferTape [] p := by
    intro p h0 h1
    simp only [List.length_nil, Nat.cast_zero] at h1
    obtain rfl : p = 0 := le_antisymm h1 h0
    rw [htape, hpos, add_zero,
      FinTM.bufferTape_eq_none_of_not_mem s (z := (s.length : ℤ)) (by omega),
      FinTM.bufferTape_nil]
  obtain ⟨h1, h2, -⟩ := skipTM_run_ofCfg (k := 2) (0 : Fin 2) [] c hst hw
  set c₁ : Cfg 2 Bool SeekPhase x := { c with
      state := some .done
      workTapePos :=
        Function.update c.workTapePos 0 (c.workTapePos 0 + ([] : List Bool).length + 1) }
    with hc₁
  obtain ⟨hpA, hA⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.aFwd j) (c := c) (c' := c₁) (([] : List Bool).length + 1) h1
    SeekPhase.done rfl ⟨.aBack j, .run⟩ rfl (by
      intro u hu q hq
      obtain rfl : u = 0 := by simp at hu; omega
      rw [MultiTapeTM.runFrom_zero, hst] at hq
      cases hq
      rfl)
  -- the redirected configuration is phase `aBack j`'s start
  have hre := nf_retag (N := N) (SL := SL) (S := nf_St N SL (nf_Ph.aFwd j)) c₁ (nf_Ph.aBack j)
    SeekPhase.run (by simp [hc₁])
  set c₂ : Cfg 2 Bool SeekPhase x := { c₁ with state := some .run } with hc₂
  -- phase `aBack j`: back over the stream to cell `0`
  have hu : ∀ p : ℤ, -1 ≤ p → p ≤ (s.length : ℤ) →
      c₂.workTapes 0 (c₂.workTapePos 0 - s.length - 1 + p) = FinTM.bufferTape s p := by
    intro p _ _
    simp only [hc₂, hc₁, Function.update_self, List.length_nil, Nat.cast_zero, hpos]
    rw [htape]
    congr 1
    ring
  obtain ⟨h3, h4, -⟩ := skipBackTM_run_ofCfg (k := 2) (0 : Fin 2) s c₂ rfl hu
  set c₃ : Cfg 2 Bool SeekPhase x := { c₂ with
      state := some .done
      workTapePos := Function.update c₂.workTapePos 0 (c₂.workTapePos 0 - s.length - 1) }
    with hc₃
  have hred : nf_red N L exit (nf_Ph.aBack j) SeekPhase.done = some (nf_aNext N L j) := by
    cases j <;> rfl
  obtain ⟨hpB, hB⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.aBack j) (c := c₂) (c' := c₃) (s.length + 3) h3
    SeekPhase.done rfl (nf_aNext N L j) hred (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h4 u hu)
      | run => cases j <;> rfl
      | gap => cases j <;> rfl
      | back => cases j <;> rfl)
  have e : s.length + 6 = (([] : List Bool).length + 1 + 1) + (s.length + 3 + 1) := by simp; omega
  refine ⟨c₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, MultiTapeTM.runFrom_add]
    unfold nf_V
    rw [hA, hre]
    exact hB
  · simp [hc₃]
  · simp only [hc₃, hc₂, hc₁, Function.update_self, List.length_nil, Nat.cast_zero, hpos]
    ring
  · simp only [hc₃, hc₂, hc₁]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · simp only [hc₃, hc₂, hc₁]
  · simp only [hc₃, hc₂, hc₁]
  · simp only [hc₃, hc₂, hc₁]
  · intro u hu b
    unfold nf_V
    by_cases hu1 : u ≤ ([] : List Bool).length + 1
    · rw [hpA u hu1]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
    · obtain ⟨v, rfl⟩ : ∃ v, u = (([] : List Bool).length + 1 + 1) + v :=
        ⟨u - (([] : List Bool).length + 1 + 1), by omega⟩
      rw [MultiTapeTM.runFrom_add, hA, hre, hpB v (by simp at hu ⊢; omega)]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b

/-- **The clear of tape `1` after a work tape's replay.** From the head of tape `1` at any offset
`i ≤ |R|` into a region `R` delimited by blanks (so `i = |R|`, the right delimiter, is allowed),
the phases `bFwd j` (`Turing.skipTM` over `R.drop i`), `bBack j` (`Turing.skipBackTM` at
`u := R`) and `bClr j` (`Turing.clearTM` over `R`) reach `nf_after N L (some j)` with tape `1`
blank on the region and its head on the region's first cell, everything else unchanged, and at no
verdict on the way.

**Proof sketch.** Chain the three framed runs through the phase lemma of the phase host,
reading each redirected configuration as the next phase's start. The region's suffix from the
head, the whole region from one past its right delimiter, and the region from its first cell are
read off the buffer of `R`. Inside each phase the host's run is tagged by that phase, which is
not the park. -/
private theorem nf_bClear (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) (exit : SL → Option Bool) {x : List Bool}
    (j : Fin N.k) (R : List Bool) (i : ℕ) (hi : i ≤ R.length)
    (c : Cfg 2 Bool SeekPhase x) (hst : c.state = some .run)
    (htape : ∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) →
      c.workTapes 1 (c.workTapePos 1 - i + p) = FinTM.bufferTape R p) :
    ∃ c₅ : Cfg 2 Bool SweepPhase x,
      (nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.bFwd j)) x).mapState (Sigma.mk (nf_Ph.bFwd j)))
          ((R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1)) =
        c₅.mapState (fun _ => nf_after N L (some j)) ∧
      c₅.state.isSome ∧
      c₅.workTapePos 1 = c.workTapePos 1 - i ∧ c₅.workTapePos 0 = c.workTapePos 0 ∧
      c₅.workTapes 0 = c.workTapes 0 ∧ c₅.inputPos = c.inputPos ∧ c₅.output = c.output ∧
      (∀ q, c₅.workTapes 1 q = if c.workTapePos 1 - i ≤ q ∧ q < c.workTapePos 1 - i + R.length
        then none else c.workTapes 1 q) ∧
      ∀ u < (R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1), ∀ b,
        ((nf_V N L exit).runFrom
          ((c : Cfg 2 Bool (nf_St N SL (nf_Ph.bFwd j)) x).mapState (Sigma.mk (nf_Ph.bFwd j)))
            u).state ≠ some ⟨.park, b⟩ := by
  have hdl : ((R.drop i).length : ℤ) = (R.length : ℤ) - i := by
    rw [List.length_drop]; push_cast [Nat.cast_sub hi]; ring
  -- phase `bFwd j`: over the region's suffix from the head
  have hw : ∀ p : ℤ, 0 ≤ p → p ≤ ((R.drop i).length : ℤ) →
      c.workTapes 1 (c.workTapePos 1 + p) = FinTM.bufferTape (R.drop i) p := by
    intro p h0 h1
    have h := htape (p + i) (by omega) (by omega)
    rw [show c.workTapePos 1 - i + (p + i) = c.workTapePos 1 + p by ring] at h
    rw [h, FinTM.bufferTape_drop R i h0, add_comm]
  obtain ⟨h1, h2, -⟩ := skipTM_run_ofCfg (k := 2) (1 : Fin 2) (R.drop i) c hst hw
  set c₁ : Cfg 2 Bool SeekPhase x := { c with
      state := some .done
      workTapePos := Function.update c.workTapePos 1 (c.workTapePos 1 + (R.drop i).length + 1) }
    with hc₁
  obtain ⟨hpA, hA⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.bFwd j) (c := c) (c' := c₁) ((R.drop i).length + 1) h1
    SeekPhase.done rfl ⟨.bBack j, .run⟩ rfl (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h2 u hu)
      | run => rfl
      | gap => rfl
      | back => rfl)
  have hre := nf_retag (N := N) (SL := SL) (S := nf_St N SL (nf_Ph.bFwd j)) c₁ (nf_Ph.bBack j)
    SeekPhase.run (by simp [hc₁])
  set c₂ : Cfg 2 Bool SeekPhase x := { c₁ with state := some .run } with hc₂
  -- phase `bBack j`: back over the whole region to its first cell
  have hu : ∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) →
      c₂.workTapes 1 (c₂.workTapePos 1 - R.length - 1 + p) = FinTM.bufferTape R p := by
    intro p h0 h1
    simp only [hc₂, hc₁, Function.update_self]
    rw [← htape p h0 h1]
    congr 1
    rw [hdl]
    ring
  obtain ⟨h3, h4, -⟩ := skipBackTM_run_ofCfg (k := 2) (1 : Fin 2) R c₂ rfl hu
  set c₃ : Cfg 2 Bool SeekPhase x := { c₂ with
      state := some .done
      workTapePos := Function.update c₂.workTapePos 1 (c₂.workTapePos 1 - R.length - 1) }
    with hc₃
  obtain ⟨hpB, hB⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.bBack j) (c := c₂) (c' := c₃) (R.length + 3) h3
    SeekPhase.done rfl ⟨.bClr j, .sweep⟩ rfl (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h4 u hu)
      | run => rfl
      | gap => rfl
      | back => rfl)
  have hpos3 : c₃.workTapePos 1 = c.workTapePos 1 - i := by
    simp only [hc₃, hc₂, hc₁, Function.update_self]
    rw [hdl]
    ring
  -- the redirected configuration is phase `bClr j`'s start
  have hre2 := nf_retag (N := N) (SL := SL) (S := nf_St N SL (nf_Ph.bBack j)) c₃ (nf_Ph.bClr j)
    SweepPhase.sweep (by simp [hc₃])
  set c₄ : Cfg 2 Bool SweepPhase x :=
    { state := some SweepPhase.sweep, inputPos := c₃.inputPos, workTapes := c₃.workTapes,
      workTapePos := c₃.workTapePos, output := c₃.output } with hc₄
  -- phase `bClr j`: blank the region
  have hcw : ∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) →
      c₄.workTapes 1 (c₄.workTapePos 1 + p) = FinTM.bufferTape R p := by
    intro p h0 h1
    have e : c₄.workTapePos 1 = c.workTapePos 1 - i := by simp only [hc₄]; exact hpos3
    rw [e]
    simp only [hc₄, hc₃, hc₂, hc₁]
    exact htape p h0 h1
  obtain ⟨h5, h6, -⟩ := clearTM_run_ofCfg (k := 2) (1 : Fin 2) R c₄ rfl hcw
  set c₅ : Cfg 2 Bool SweepPhase x := { c₄ with
      state := some SweepPhase.done
      workTapes := fun j q =>
        if j = 1 ∧ c₄.workTapePos j ≤ q ∧ q < c₄.workTapePos j + (R.length : ℤ)
          then none
        else c₄.workTapes j q } with hc₅
  obtain ⟨hpC, hC⟩ := phaseHostTM_run (nf_M N L) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N L exit) (nf_Ph.bClr j) (c := c₄) (c' := c₅) (2 * R.length + 2) h5
    SweepPhase.done rfl (nf_after N L (some j)) rfl (by
      intro u hu q hq
      cases q with
      | done => exact absurd hq (h6 u hu)
      | sweep => rfl
      | rewind => rfl)
  have e : (R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1) =
      ((R.drop i).length + 1 + 1) + ((R.length + 3 + 1) + (2 * R.length + 2 + 1)) := by
    rw [List.length_drop]; omega
  refine ⟨c₅, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e, MultiTapeTM.runFrom_add]
    unfold nf_V
    rw [hA, hre, MultiTapeTM.runFrom_add, hB, hre2]
    exact hC
  · simp [hc₅]
  · simp only [hc₅, hc₄]
    exact hpos3
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
    rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide)]
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
    funext q
    rw [if_neg (fun h => absurd h.1 (by decide))]
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
  · simp only [hc₅, hc₄, hc₃, hc₂, hc₁]
  · intro q
    have e4 : c₄.workTapePos 1 = c.workTapePos 1 - i := by simp only [hc₄]; exact hpos3
    have ew : c₄.workTapes 1 q = c.workTapes 1 q := by simp only [hc₄, hc₃, hc₂, hc₁]
    have hq : c₅.workTapes 1 q = if (1 : Fin 2) = 1 ∧ c₄.workTapePos 1 ≤ q ∧
        q < c₄.workTapePos 1 + (R.length : ℤ) then none else c₄.workTapes 1 q := rfl
    rw [hq, e4, ew]
    by_cases h : c.workTapePos 1 - i ≤ q ∧ q < c.workTapePos 1 - i + R.length
    · rw [if_pos ⟨rfl, h⟩, if_pos h]
    · rw [if_neg (fun h' => h h'.2), if_neg h]
  · intro u hu b
    unfold nf_V
    by_cases hu1 : u ≤ (R.drop i).length + 1
    · rw [hpA u hu1]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
    · obtain ⟨v, rfl⟩ : ∃ v, u = ((R.drop i).length + 1 + 1) + v :=
        ⟨u - ((R.drop i).length + 1 + 1), by omega⟩
      rw [MultiTapeTM.runFrom_add, hA, hre]
      by_cases hv1 : v ≤ R.length + 3
      · rw [hpB v hv1]
        exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
      · obtain ⟨w, rfl⟩ : ∃ w, v = (R.length + 3 + 1) + w := ⟨v - (R.length + 3 + 1), by omega⟩
        rw [MultiTapeTM.runFrom_add, hB, hre2, hpC w (by rw [List.length_drop] at hu; omega)]
        exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b

/-- **The verifier's entry is the stream start.** After the trivial setup, the run's entry
configuration is `streamStartCfg x 0 q s`: state `q`, the input head at `1`, `s` on tape `0`
from cell `0` (blank elsewhere), tape `1` blank, both heads at `0`, empty output.

**Proof sketch.** Compare the two configurations field by field through their field equations.
On tape `0` the guessed block over the blank initial tape is the buffer of `s`: inside the block
by definition, and outside it both are blank (left of cell `0`, and past the end of `s`). -/
private theorem nf_entry {SP S : Type} (P : MultiTapeTM 2 Bool SP) (x s : List Bool) (q : S) :
    guessRunCfg (P.initCfg x) 0 s q = streamStartCfg x 0 q s := by
  rw [MultiTapeTM.initCfg_eq]
  apply Cfg.ext
  · rw [guessRunCfg_state, streamStartCfg_state]
  · rw [guessRunCfg_inputPos, streamStartCfg_inputPos, Cfg.init_inputPos]
  · funext i p
    rw [guessRunCfg_workTapes, streamStartCfg_workTapes, Cfg.init_workTapePos]
    by_cases hi : i = 0
    · subst hi
      rw [Function.update_self, if_pos rfl]
      by_cases hp : (0 : ℤ) ≤ p ∧ p < 0 + (s.length : ℤ)
      · rw [if_pos hp, sub_zero]
      · rw [if_neg hp, Cfg.init_workTapes]
        rw [FinTM.bufferTape_eq_none_of_not_mem s (by omega)]
    · rw [Function.update_of_ne hi, if_neg hi, Cfg.init_workTapes]
  · funext i
    rw [guessRunCfg_workTapePos, streamStartCfg_workTapePos, Cfg.init_workTapePos]
  · rw [guessRunCfg_output, streamStartCfg_output, Cfg.init_output]

/-- A stream-start configuration with a tagged state is the tagged stream start. -/
private theorem nf_tag {N : FinNDTM Bool} {SL : Type} (x s : List Bool) (i : nf_Ph N.k)
    (q : nf_St N SL i) :
    streamStartCfg x (0 : Fin 2) (⟨i, q⟩ : Σ i, nf_St N SL i) s =
      (streamStartCfg x (0 : Fin 2) q s).mapState (Sigma.mk i) :=
  (Cfg.mapState_eq_of_fields _ _ _
    (by rw [streamStartCfg_state, streamStartCfg_state]; rfl)
    (by rw [streamStartCfg_inputPos, streamStartCfg_inputPos])
    (by funext j p; rw [streamStartCfg_workTapes, streamStartCfg_workTapes])
    (by funext j; rw [streamStartCfg_workTapePos, streamStartCfg_workTapePos])
    (by rw [streamStartCfg_output, streamStartCfg_output])).symm

/-- After a record's first `2k + 3` bits the parser is at the last position with the control
unchanged; the record's last bit completes the full record array, and the parser's step there
resets the parser and applies the completion rule to that record.

**Proof sketch.** The prefix law of the parser gives the position and the stored prefix. Storing
the last bit fills the only missing entry, and the whole-record law, split at its last bit, is
the parser's last step. -/
private theorem nf_prefix_last (N : FinNDTM Bool) (rec : Fin (2 * N.k + 4) → Bool)
    (ctl : nf_Control N) (σ : nf_SweepState N)
    (hσ : σ = (List.ofFn fun i : Fin (2 * N.k + 3) => rec ⟨i.val, by omega⟩).foldl
      (nf_sweepStep N) ((0, fun _ => none), ctl)) :
    σ.1.1.val = 2 * N.k + 3 ∧ σ.2 = ctl ∧
      Function.update σ.1.2 σ.1.1 (some (rec ⟨2 * N.k + 3, by omega⟩)) =
        (fun p => some (rec p)) ∧
      nf_sweepStep N σ (rec ⟨2 * N.k + 3, by omega⟩) =
        ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl) := by
  have hp := nf_sweep_prefix N rec ctl (2 * N.k + 3) (by omega)
  rw [← hσ] at hp
  refine ⟨by rw [hp], by rw [hp], ?_, ?_⟩
  · rw [hp]
    exact nf_update_last N rec
  · have h := nf_sweep_record N rec ctl
    rw [List.ofFn_succ_last, List.foldl_concat] at h
    rw [hσ]
    exact h

/-- **The replay leaf reads a record's bits.** From a record boundary, with the record's bits on
tape `0` from its head, the leaf takes one step per bit, moving that head right and storing the
bit in the control sweep's parser, and changes nothing else, for every instance.

**Proof sketch.** Induct on the number of bits read. Before the record's last bit the parser's
position is not the last one, so the leaf's table is a one-tape right move on tape `0` that
stores the scanned bit; the stored prefix grows by that bit, and the head of tape `0` by one
cell. -/
private theorem nf_leaf_prefix (N : FinNDTM Bool) (j : Option (Fin N.k)) {x : List Bool}
    (d : Cfg 2 Bool (nf_LeafSt N) x) (rec : Fin (2 * N.k + 4) → Bool) (ctl : nf_Control N)
    (hst : d.state = some (.read ((0, fun _ => none), ctl)))
    (hA : ∀ p : Fin (2 * N.k + 4), d.workTapes 0 (d.workTapePos 0 + (p.val : ℤ)) = some (rec p)) :
    ∀ (m : ℕ) (hm : m < 2 * N.k + 4), (nf_leaf N j).runFrom d m = { d with
      state := some (.read ((List.ofFn fun i : Fin m => rec ⟨i.val, by omega⟩).foldl
        (nf_sweepStep N) ((0, fun _ => none), ctl)))
      workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + m) }
  | 0, _ => by
    rw [MultiTapeTM.runFrom_zero]
    apply Cfg.ext
    · rw [hst]
      rfl
    · rfl
    · rfl
    · funext i
      show d.workTapePos i = Function.update d.workTapePos 0 (d.workTapePos 0 + ((0 : ℕ) : ℤ)) i
      rw [Nat.cast_zero, add_zero, Function.update_eq_self]
    · rfl
  | m + 1, hm => by
    rw [MultiTapeTM.runFrom_succ_eq_step', nf_leaf_prefix N j d rec ctl hst hA m (by omega)]
    have hp := nf_sweep_prefix N rec ctl m (by omega)
    have hm1 : ((List.ofFn fun i : Fin m => rec ⟨i.val, by omega⟩).foldl
        (nf_sweepStep N) ((0, fun _ => none), ctl)).1.1.val = m := by rw [hp]
    have hsym : ({ d with
        state := some (.read ((List.ofFn fun i : Fin m => rec ⟨i.val, by omega⟩).foldl
          (nf_sweepStep N) ((0, fun _ => none), ctl)))
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + m) } :
          Cfg 2 Bool (nf_LeafSt N) x).workTapeSymbols 0 = some (rec ⟨m, by omega⟩) := by
      rw [Cfg.workTapeSymbols_eq]
      show d.workTapes 0 (Function.update d.workTapePos 0 (d.workTapePos 0 + m) 0) = _
      rw [Function.update_self]
      exact hA ⟨m, by omega⟩
    rw [step_of_tapeAction_move (nf_leaf N j) _ (q := .read _) 0 0 1 rfl (by
      simp only [nf_leaf]
      rw [if_neg (by rw [hm1]; omega), hsym, Option.getD_some])]
    apply Cfg.ext
    · show some (nf_LeafSt.read (nf_sweepStep N _ _)) = some (nf_LeafSt.read
        ((List.ofFn fun i : Fin (m + 1) => rec ⟨i.val, by omega⟩).foldl
          (nf_sweepStep N) ((0, fun _ => none), ctl)))
      rw [List.ofFn_succ_last, List.foldl_concat]
      simp only [Fin.coe_castSucc, Fin.val_last, hp]
    · exact moveInputPos_zero _
    · rfl
    · funext i
      dsimp only
      by_cases hi : i = 0
      · subst hi
        rw [Function.update_self, Function.update_self, Function.update_self, SignType.coe_one]
        push_cast
        ring
      · rw [Function.update_of_ne hi, Function.update_of_ne hi, Function.update_of_ne hi]
    · rfl

/-- **The replay leaf at a record's last bit.** From a record boundary, with the record on tape `0`
from its head, every instance is at no exit for the record's first `2k + 4` steps; after `2k + 3`
of them it reads the last bit with the parser at its last position, the record's array complete
once that bit is stored, and the parser's step there the completion rule.

**Proof sketch.** The read of the first `2k + 3` bits, then the parser's last-position facts. -/
private theorem nf_leaf_toLast (N : FinNDTM Bool) (j : Option (Fin N.k)) {x : List Bool}
    (d : Cfg 2 Bool (nf_LeafSt N) x) (rec : Fin (2 * N.k + 4) → Bool) (ctl : nf_Control N)
    (hst : d.state = some (.read ((0, fun _ => none), ctl)))
    (hA : ∀ p : Fin (2 * N.k + 4), d.workTapes 0 (d.workTapePos 0 + (p.val : ℤ)) = some (rec p)) :
    (∀ u < 2 * N.k + 4, ∀ s, ((nf_leaf N j).runFrom d u).state = some s →
      nf_leafExit N s = none) ∧
    ∃ σ : nf_SweepState N, σ.1.1.val = 2 * N.k + 3 ∧ σ.2 = ctl ∧
      Function.update σ.1.2 σ.1.1 (some (rec ⟨2 * N.k + 3, by omega⟩)) =
        (fun p => some (rec p)) ∧
      nf_sweepStep N σ (rec ⟨2 * N.k + 3, by omega⟩) =
        ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl) ∧
      (nf_leaf N j).runFrom d (2 * N.k + 4) = (nf_leaf N j).step { d with
        state := some (.read σ)
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) } ∧
      ({ d with
        state := some (.read σ)
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) } :
          Cfg 2 Bool (nf_LeafSt N) x).workTapeSymbols 0 = some (rec ⟨2 * N.k + 3, by omega⟩) := by
  have hpre := nf_leaf_prefix N j d rec ctl hst hA
  refine ⟨fun u hu s hs => ?_, ?_⟩
  · rw [hpre u hu] at hs
    cases hs
    rfl
  set σ := (List.ofFn fun i : Fin (2 * N.k + 3) => rec ⟨i.val, by omega⟩).foldl
    (nf_sweepStep N) ((0, fun _ => none), ctl) with hσ
  obtain ⟨h1, h2, h3, h4⟩ := nf_prefix_last N rec ctl σ hσ
  refine ⟨σ, h1, h2, h3, h4, ?_, ?_⟩
  · rw [show 2 * N.k + 4 = (2 * N.k + 3) + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step',
      hpre (2 * N.k + 3) (by omega)]
  · rw [Cfg.workTapeSymbols_eq]
    show d.workTapes 0 (Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) 0) = _
    rw [Function.update_self]
    exact hA ⟨2 * N.k + 3, by omega⟩

/-- **One record of the input's replay.** From a record boundary, with the record on tape `0`
from its head, the input instance reads the record in `2k + 4` steps, at no exit before. At a
live control whose decoded input claim is the cell under the native input head, it performs the
recomputed input move, its head on tape `0` is one cell past the record, and it is at the next
record boundary, or passes if the record is end-flagged; otherwise it rejects.

**Proof sketch.** Up to the record's last bit the leaf reads the record, and there the parser
completes it. The leaf's table, read at the control's state and at the native input cell (which
depends on the input head only), is then a one-tape action: a move of the input head and of the
head of tape `0`, or a stationary rejection. -/
private theorem nf_leaf_record_in (N : FinNDTM Bool) {x : List Bool}
    (d : Cfg 2 Bool (nf_LeafSt N) x) (rec : Fin (2 * N.k + 4) → Bool) (ctl : nf_Control N)
    (hst : d.state = some (.read ((0, fun _ => none), ctl)))
    (hA : ∀ p : Fin (2 * N.k + 4), d.workTapes 0 (d.workTapePos 0 + (p.val : ℤ)) = some (rec p)) :
    (∀ u < 2 * N.k + 4, ∀ s, ((nf_leaf N none).runFrom d u).state = some s →
      nf_leafExit N s = none) ∧
    (∀ q, ctl.1 = some q → nf_decode N.k (fun p => some (rec p)) 0 = d.inputSymbol →
      (nf_leaf N none).runFrom d (2 * N.k + 4) = { d with
        state := some (if rec ⟨2 * N.k + 3, by omega⟩ then .pass
          else .read ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl))
        inputPos := moveInputPos d.inputPos (nf_act N (fun p => some (rec p)) q).inputTape
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) }) ∧
    ((ctl.1 = none ∨ nf_decode N.k (fun p => some (rec p)) 0 ≠ d.inputSymbol) →
      ((nf_leaf N none).runFrom d (2 * N.k + 4)).state = some .rej) := by
  obtain ⟨hpre, σ, h1, h2, h3, h4, hrun, hsym⟩ := nf_leaf_toLast N none d rec ctl hst hA
  refine ⟨hpre, ?_⟩
  set c : Cfg 2 Bool (nf_LeafSt N) x := { d with
      state := some (.read σ)
      workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) }
    with hc
  have hinp : c.inputSymbol = d.inputSymbol := Cfg.inputSymbol_congr c d rfl
  refine ⟨fun q hq hdec => ?_, fun hbad => ?_⟩
  · rw [hrun, step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) 0 _ 1 rfl (by
      simp only [nf_leaf]
      rw [if_pos h1, h2, hq]
      dsimp only
      rw [hsym, Option.getD_some, h3, hinp, if_pos hdec])]
    apply Cfg.ext
    · show some (if rec ⟨2 * N.k + 3, by omega⟩ then nf_LeafSt.pass
        else nf_LeafSt.read (nf_sweepStep N σ (rec ⟨2 * N.k + 3, by omega⟩))) = _
      rw [h4]
    · rfl
    · rfl
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [hc, Function.update_self, SignType.coe_one]
        push_cast
        ring
      · simp only [hc, Function.update_of_ne hi]
    · rfl
  · rw [hrun]
    rcases hbad with hn | hdec
    · rw [step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) (q' := .rej) 0 0 0 rfl (by
        simp only [nf_leaf]
        rw [if_pos h1, h2, hn])]
    · cases hq : ctl.1 with
      | none =>
        rw [step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) (q' := .rej) 0 0 0 rfl (by
          simp only [nf_leaf]
          rw [if_pos h1, h2, hq])]
      | some q =>
        rw [step_of_tapeAction_move (nf_leaf N none) c (q := .read σ) (q' := .rej) 0 0 0 rfl (by
          simp only [nf_leaf]
          rw [if_pos h1, h2, hq]
          dsimp only
          rw [hsym, Option.getD_some, h3, hinp, if_neg hdec])]

/-- **The decoded virtual step of `N`.** At a live state, apply the action recomputed from a
record's decoded claims (`nf_act`); a halted configuration stays. When every claim is the
configuration's read, it is `N`'s step under the record's choice bit (`nf_vrun_of_ok`). -/
private def nf_vstep (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (rec : Fin (2 * N.k + 4) → Bool) : Cfg N.k Bool N.State x :=
  match c.state with
  | none => c
  | some q => (nf_act N (fun p => some (rec p)) q).apply c

/-- A record's claim on replayed tape `i` (`0` the input, `j.succ` work tape `j`) is checked: the
virtual configuration is live and the decoded claim is its read on that tape. -/
private def nf_ok (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (rec : Fin (2 * N.k + 4) → Bool) (i : Fin (N.k + 1)) : Prop :=
  c.state ≠ none ∧
    nf_decode N.k (fun p => some (rec p)) i =
      (Fin.cases c.inputSymbol c.workTapeSymbols : Fin (N.k + 1) → Option Bool) i

/-- The control fold's state follows the decoded virtual run, one record at a time. -/
private theorem nf_vstep_state (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (ctl : nf_Control N) (rec : Fin (2 * N.k + 4) → Bool) (h1 : ctl.1 = c.state) :
    (nf_complete N (fun p => some (rec p)) ctl).1 = (nf_vstep N c rec).state := by
  obtain ⟨cs, o, f⟩ := ctl
  simp only at h1
  subst h1
  cases hc : c.state with
  | none => simp only [nf_complete, nf_vstep, hc]
  | some q =>
    simp only [nf_complete, nf_vstep, hc]
    exact (Action.apply_state _ _).symm

/-- The control fold's state and output summary follow the decoded virtual run.

**Proof sketch.** Case on the virtual state. Halted, both stay. Live, the completion rule and
the virtual step apply the same recomputed action, and appending the action's emission updates
the output summary as the completion rule does. -/
private theorem nf_vstep_ctl (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (ctl : nf_Control N) (rec : Fin (2 * N.k + 4) → Bool) (h1 : ctl.1 = c.state)
    (h2 : ctl.2.1 = StepBlock.outputSummary c.output) :
    (nf_complete N (fun p => some (rec p)) ctl).1 = (nf_vstep N c rec).state ∧
      (nf_complete N (fun p => some (rec p)) ctl).2.1 =
        StepBlock.outputSummary (nf_vstep N c rec).output := by
  refine ⟨nf_vstep_state N c ctl rec h1, ?_⟩
  obtain ⟨cs, o, f⟩ := ctl
  simp only at h1 h2
  subst h1 h2
  cases hc : c.state with
  | none => simp only [nf_complete, nf_vstep, hc]
  | some q =>
    simp only [nf_complete, nf_vstep, hc]
    rw [Action.apply_output, StepBlock.outputSummary_append]
    rfl

/-- The control fold's state and output summary follow the decoded virtual run, over a list of
records. -/
private theorem nf_vrun_ctl (N : FinNDTM Bool) {x : List Bool} :
    ∀ (rs : List (Fin (2 * N.k + 4) → Bool)) (c : Cfg N.k Bool N.State x) (ctl : nf_Control N),
      ctl.1 = c.state → ctl.2.1 = StepBlock.outputSummary c.output →
      (rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) ctl).1 =
          (rs.foldl (nf_vstep N) c).state ∧
        (rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) ctl).2.1 =
          StepBlock.outputSummary (rs.foldl (nf_vstep N) c).output
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | rec :: rs, c, ctl, h1, h2 => by
    obtain ⟨e1, e2⟩ := nf_vstep_ctl N c ctl rec h1 h2
    exact nf_vrun_ctl N rs _ _ e1 e2

/-- A stream of records, one record and the rest: its cells from a head are the record's bits
and then the rest's cells one record further.

**Proof sketch.** The stream is the record's bits followed by the rest's stream; read a cell
before the record's end in the first part and a later cell in the second, shifted by the record
width. -/
private theorem nf_stream_cons (k : ℕ) (rec : Fin (2 * k + 4) → Bool)
    (rs : List (Fin (2 * k + 4) → Bool)) (T : ℤ → Option Bool) (h : ℤ)
    (hT : ∀ p : ℕ, p < ((rec :: rs).flatMap List.ofFn).length →
      T (h + p) = ((rec :: rs).flatMap List.ofFn)[p]?) :
    (∀ p : Fin (2 * k + 4), T (h + (p.val : ℤ)) = some (rec p)) ∧
      ∀ p : ℕ, p < (rs.flatMap List.ofFn).length →
        T (h + ((2 * k + 4 : ℕ) : ℤ) + p) = (rs.flatMap List.ofFn)[p]? := by
  rw [List.flatMap_cons] at hT
  refine ⟨fun p => ?_, fun p hp => ?_⟩
  · have hlt : p.val < (List.ofFn rec ++ rs.flatMap List.ofFn).length := by
      rw [List.length_append, List.length_ofFn]; omega
    rw [hT p.val hlt, List.getElem?_append_left (by rw [List.length_ofFn]; exact p.isLt),
      List.getElem?_ofFn]
    simp
  · have hlt : (2 * k + 4) + p < (List.ofFn rec ++ rs.flatMap List.ofFn).length := by
      rw [List.length_append, List.length_ofFn]; omega
    have e := hT ((2 * k + 4) + p) hlt
    rw [List.getElem?_append_right (by rw [List.length_ofFn]; omega), List.length_ofFn,
      Nat.add_sub_cancel_left] at e
    rw [← e]
    congr 1
    push_cast
    ring

/-- Every record of `rec :: rs` meets a check along the virtual run from `c` exactly when `rec`
meets it at `c` and every record of `rs` meets it along the run from the virtual step. -/
private theorem nf_all_cons (N : FinNDTM Bool) {x : List Bool} (c : Cfg N.k Bool N.State x)
    (rec : Fin (2 * N.k + 4) → Bool) (rs : List (Fin (2 * N.k + 4) → Bool))
    (P : Cfg N.k Bool N.State x → (Fin (2 * N.k + 4) → Bool) → Prop) :
    (∀ r (h : r < (rec :: rs).length),
      P (((rec :: rs).take r).foldl (nf_vstep N) c) (rec :: rs)[r]) ↔
      P c rec ∧ ∀ r (h : r < rs.length),
        P ((rs.take r).foldl (nf_vstep N) (nf_vstep N c rec)) rs[r] :=
  Nat.forall_lt_succ_left'

/-- In a stream of records whose end flags mark exactly the last, the first record's flag says
whether it is the only one, and the rest's flags mark exactly the rest's last. -/
private theorem nf_flags_cons {k : ℕ} (rec : Fin (2 * k + 4) → Bool)
    (rs : List (Fin (2 * k + 4) → Bool))
    (hflag : ∀ r (h : r < (rec :: rs).length),
      (rec :: rs)[r] ⟨2 * k + 3, by omega⟩ = decide (r + 1 = (rec :: rs).length)) :
    rec ⟨2 * k + 3, by omega⟩ = decide (rs = []) ∧
      ∀ r (h : r < rs.length), rs[r] ⟨2 * k + 3, by omega⟩ = decide (r + 1 = rs.length) := by
  refine ⟨?_, fun r hr => ?_⟩
  · have := hflag 0 (by simp)
    simp only [List.getElem_cons_zero, List.length_cons, zero_add] at this
    rw [this]
    cases rs <;> simp
  · have := hflag (r + 1) (by simp; omega)
    simpa using this

/-- **The input's replay.** From a record boundary with a stream of `n ≥ 1` records on tape `0`
from its head, only the last end-flagged, at a control that follows the virtual configuration
`c` whose input head is the native one, the input instance reaches an exit at some time `T`, at
no exit before. It passes exactly when every record's input claim is checked along the decoded
virtual run; then `T = (2k + 4)n`, its head on tape `0` is one cell past the stream, and only
that head, the input head and the state have changed. Otherwise it rejects.

**Proof sketch.** Induct over the records, one record at a time: a failed check rejects at the
record's end; a passed check of the end-flagged record passes; a passed check of an unflagged
record moves the input head as the virtual step does, keeps the control equal to the virtual
run's state, and leaves the rest of the stream one record further on, where the induction
hypothesis applies. -/
private theorem nf_leaf_run_in (N : FinNDTM Bool) {x : List Bool} :
    ∀ (rs : List (Fin (2 * N.k + 4) → Bool)) (d : Cfg 2 Bool (nf_LeafSt N) x)
      (ctl : nf_Control N) (c : Cfg N.k Bool N.State x),
    rs ≠ [] →
    (∀ r (h : r < rs.length), rs[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = rs.length)) →
    d.state = some (.read ((0, fun _ => none), ctl)) → ctl.1 = c.state →
    d.inputPos = c.inputPos →
    (∀ p : ℕ, p < (rs.flatMap List.ofFn).length →
      d.workTapes 0 (d.workTapePos 0 + p) = (rs.flatMap List.ofFn)[p]?) →
    ∃ T, (∀ u < T, ∀ s, ((nf_leaf N none).runFrom d u).state = some s →
        nf_leafExit N s = none) ∧
      ((∀ r (h : r < rs.length), nf_ok N ((rs.take r).foldl (nf_vstep N) c) rs[r] 0) →
        T = (2 * N.k + 4) * rs.length ∧ ∃ ip, (nf_leaf N none).runFrom d T = { d with
          state := some .pass
          inputPos := ip
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + ((2 * N.k + 4) * rs.length : ℕ)) }) ∧
      (¬ (∀ r (h : r < rs.length), nf_ok N ((rs.take r).foldl (nf_vstep N) c) rs[r] 0) →
        ((nf_leaf N none).runFrom d T).state = some .rej)
  | [], _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | rec :: rs, d, ctl, c, _, hflag, hst, hc, hip, hA => by
    obtain ⟨hA0, hA1⟩ := nf_stream_cons N.k rec rs (d.workTapes 0) (d.workTapePos 0) hA
    obtain ⟨hpre, hpass, hrej⟩ := nf_leaf_record_in N d rec ctl hst hA0
    have hinp : d.inputSymbol = c.inputSymbol := Cfg.inputSymbol_congr d c (by rw [hip])
    have hall := nf_all_cons N c rec rs (fun c rec => nf_ok N c rec 0)
    obtain ⟨hfl, hflag'⟩ := nf_flags_cons rec rs hflag
    by_cases hok : nf_ok N c rec 0
    · obtain ⟨hlive, hdec⟩ := hok
      obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlive
      have hdec' : nf_decode N.k (fun p => some (rec p)) 0 = d.inputSymbol := by
        rw [hinp, hdec]; rfl
      have hrun := hpass q (hc.trans hq) hdec'
      cases rs with
      | nil =>
        have hl : rec ⟨2 * N.k + 3, by omega⟩ = true := by simpa using hfl
        refine ⟨2 * N.k + 4, hpre, fun _ => ⟨by simp,
          moveInputPos d.inputPos (nf_act N (fun p => some (rec p)) q).inputTape, ?_⟩,
          fun hn => absurd ?_ hn⟩
        · rw [hrun, if_pos hl]
          simp
        · intro r hr
          simp at hr
          subst hr
          exact ⟨hlive, hdec⟩
      | cons rec' rs' =>
        have hl : rec ⟨2 * N.k + 3, by omega⟩ = false := by simpa using hfl
        rw [if_neg (by simp [hl])] at hrun
        set d' : Cfg 2 Bool (nf_LeafSt N) x := { d with
          state := some (.read ((0, fun _ => none),
            nf_complete N (fun p => some (rec p)) ctl))
          inputPos := moveInputPos d.inputPos (nf_act N (fun p => some (rec p)) q).inputTape
          workTapePos := Function.update d.workTapePos 0
            (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) } with hd'
        have hvc := nf_vstep_state N c ctl rec hc
        have hvip : d'.inputPos = (nf_vstep N c rec).inputPos := by
          show moveInputPos d.inputPos _ = _
          simp only [nf_vstep, hq]
          rw [Action.apply_inputPos, hip]
        have hA' : ∀ p : ℕ, p < ((rec' :: rs').flatMap List.ofFn).length →
            d'.workTapes 0 (d'.workTapePos 0 + p) = ((rec' :: rs').flatMap List.ofFn)[p]? := by
          intro p hp
          show d.workTapes 0 (Function.update d.workTapePos 0
            (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) 0 + p) = _
          rw [Function.update_self]
          exact hA1 p hp
        obtain ⟨T', hpre', hpass', hrej'⟩ := nf_leaf_run_in N (rec' :: rs') d'
          (nf_complete N (fun p => some (rec p)) ctl) (nf_vstep N c rec) (by simp) hflag' rfl hvc
          hvip hA'
        refine ⟨(2 * N.k + 4) + T', fun u hu s hs => ?_, fun h => ?_, fun h => ?_⟩
        · by_cases hu1 : u < 2 * N.k + 4
          · exact hpre u hu1 s hs
          · obtain ⟨v, rfl⟩ : ∃ v, u = (2 * N.k + 4) + v := ⟨u - (2 * N.k + 4), by omega⟩
            rw [MultiTapeTM.runFrom_add, hrun] at hs
            exact hpre' v (by omega) s hs
        · obtain ⟨hT, ip, hcfg⟩ := hpass' ((hall.mp h).2)
          refine ⟨by rw [hT]; simp; ring, ip, ?_⟩
          rw [MultiTapeTM.runFrom_add, hrun, hcfg]
          apply Cfg.ext
          · rfl
          · rfl
          · rfl
          · funext i
            by_cases hi : i = 0
            · subst hi
              simp only [hd', Function.update_self, List.length_cons]
              push_cast
              ring
            · simp only [hd', Function.update_of_ne hi]
          · rfl
        · have hn : ¬ ∀ r (h : r < (rec' :: rs').length),
              nf_ok N (((rec' :: rs').take r).foldl (nf_vstep N) (nf_vstep N c rec))
                (rec' :: rs')[r] 0 := fun h' => h (hall.mpr ⟨⟨hlive, hdec⟩, h'⟩)
          rw [MultiTapeTM.runFrom_add, hrun]
          exact hrej' hn
    · refine ⟨2 * N.k + 4, hpre, fun h => absurd ((hall.mp h).1) hok, fun _ => hrej ?_⟩
      by_cases hl : c.state = none
      · exact Or.inl (hc.trans hl)
      · refine Or.inr fun hdec => hok ⟨hl, ?_⟩
        rw [hdec, hinp]
        rfl

/-- Tape `1` with the block at cell `b` rewritten to hold the content `n`: two nonblank bits,
`nf_record`'s code of `n`. -/
private def nf_blockWrite (B : ℤ → Option Bool) (b : ℤ) (n : Option Bool) : ℤ → Option Bool :=
  Function.update (Function.update B b (some n.isSome)) (b + 1) (some (n.getD false))

/-- **One block of a work tape's replay.** At the first cell `b` of the block on tape `1`, the
work-tape instance reads the block's two cells, rewriting them to the cell's new content `n`, in
two steps. If the block decodes to the claim, then after the end-flagged record it passes, its
head on the block's second cell; after any other record two more steps leave that head at
`b + 2 mv`, at the next record boundary. Otherwise it rejects. Tape `0`, its head, the input head
and the output do not change, and there is no exit before.

**Proof sketch.** Each of the four steps is a one-tape action of the leaf's table on tape `1`:
two writing steps, the second of which checks the block read off the first step's old cell and
the second cell (unchanged by the first write), then two moves. The head of tape `1` moves by
`+1`, then `+1` or `−1`, then `0` or `−1` twice, which sums to two cells per simulated move. -/
private theorem nf_leaf_block (N : FinNDTM Bool) (t : Fin N.k) {x : List Bool}
    (e : Cfg 2 Bool (nf_LeafSt N) x) (σ : nf_SweepState N) (claim n : Option Bool)
    (mv : SignType) (last : Bool) (hst : e.state = some (.blk₁ σ claim n mv last)) :
    (∀ u < 2, ∀ s, ((nf_leaf N (some t)).runFrom e u).state = some s →
      nf_leafExit N s = none) ∧
    (nf_blockDecode (e.workTapes 1 (e.workTapePos 1)) (e.workTapes 1 (e.workTapePos 1 + 1)) =
        claim → last = true →
      (nf_leaf N (some t)).runFrom e 2 = { e with
        state := some .pass
        workTapes :=
          Function.update e.workTapes 1 (nf_blockWrite (e.workTapes 1) (e.workTapePos 1) n)
        workTapePos := Function.update e.workTapePos 1 (e.workTapePos 1 + 1) }) ∧
    (nf_blockDecode (e.workTapes 1 (e.workTapePos 1)) (e.workTapes 1 (e.workTapePos 1 + 1)) =
        claim → last = false →
      (∀ u < 4, ∀ s, ((nf_leaf N (some t)).runFrom e u).state = some s →
        nf_leafExit N s = none) ∧
      (nf_leaf N (some t)).runFrom e 4 = { e with
        state := some (.read σ)
        workTapes :=
          Function.update e.workTapes 1 (nf_blockWrite (e.workTapes 1) (e.workTapePos 1) n)
        workTapePos := Function.update e.workTapePos 1 (e.workTapePos 1 + 2 * (mv : ℤ)) }) ∧
    (nf_blockDecode (e.workTapes 1 (e.workTapePos 1)) (e.workTapes 1 (e.workTapePos 1 + 1)) ≠
        claim → ((nf_leaf N (some t)).runFrom e 2).state = some .rej) := by
  set b := e.workTapePos 1 with hb
  -- the first block step: read the first cell, write the content's first bit, move right
  set e₁ : Cfg 2 Bool (nf_LeafSt N) x := { e with
      state := some (.blk₂ σ claim n mv last (e.workTapes 1 b))
      inputPos := moveInputPos e.inputPos 0
      workTapes := Function.update e.workTapes 1
        (Function.update (e.workTapes 1) (e.workTapePos 1) (some n.isSome))
      workTapePos := Function.update e.workTapePos 1 (e.workTapePos 1 + 1) } with he₁
  have h1 : (nf_leaf N (some t)).runFrom e 1 = e₁ := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_zero,
      step_of_tapeAction_write (nf_leaf N (some t)) e (q := .blk₁ σ claim n mv last) 1 0
        (some n.isSome) 1 hst rfl, SignType.coe_one, Cfg.workTapeSymbols_eq]
  have hsym1 : e₁.workTapeSymbols 1 = e.workTapes 1 (b + 1) := by
    rw [Cfg.workTapeSymbols_eq]
    show Function.update e.workTapes 1
      (Function.update (e.workTapes 1) (e.workTapePos 1) (some n.isSome)) 1
      (Function.update e.workTapePos 1 (e.workTapePos 1 + 1) 1) = _
    rw [Function.update_self, Function.update_self, Function.update_of_ne (by omega)]
  have hpre : ∀ u < 2, ∀ s, ((nf_leaf N (some t)).runFrom e u).state = some s →
      nf_leafExit N s = none := by
    intro u hu s hs
    rcases (by omega : u = 0 ∨ u = 1) with rfl | rfl
    · rw [MultiTapeTM.runFrom_zero, hst] at hs
      cases hs
      rfl
    · rw [h1] at hs
      cases hs
      rfl
  have hw2 : ∀ (q' : nf_LeafSt N) (m : SignType) (v : Bool),
      (nf_leaf N (some t)).tr (.blk₂ σ claim n mv last (e.workTapes 1 b)) e₁.inputSymbol
        e₁.workTapeSymbols = tapeAction 1 0 (some (some v)) m q' →
      (nf_leaf N (some t)).runFrom e 2 = { e₁ with
        state := some q'
        inputPos := moveInputPos e₁.inputPos 0
        workTapes := Function.update e₁.workTapes 1
          (Function.update (e₁.workTapes 1) (e₁.workTapePos 1) (some v))
        workTapePos := Function.update e₁.workTapePos 1 (e₁.workTapePos 1 + m) } := by
    intro q' m v htr
    have e2 : (nf_leaf N (some t)).runFrom e 2 =
        (nf_leaf N (some t)).step ((nf_leaf N (some t)).runFrom e 1) :=
      MultiTapeTM.runFrom_succ_eq_step'
    rw [e2, h1,
      step_of_tapeAction_write (nf_leaf N (some t)) e₁ (q := .blk₂ σ claim n mv last
        (e.workTapes 1 b)) 1 0 (some v) m rfl htr]
  have htape2 : Function.update e₁.workTapes 1
      (Function.update (e₁.workTapes 1) (e₁.workTapePos 1) (some (n.getD false))) =
        Function.update e.workTapes 1 (nf_blockWrite (e.workTapes 1) b n) := by
    show Function.update (Function.update e.workTapes 1
      (Function.update (e.workTapes 1) (e.workTapePos 1) (some n.isSome))) 1
      (Function.update (Function.update e.workTapes 1
        (Function.update (e.workTapes 1) (e.workTapePos 1) (some n.isSome)) 1)
        (Function.update e.workTapePos 1 (e.workTapePos 1 + 1) 1) (some (n.getD false))) = _
    rw [Function.update_self, Function.update_self, Function.update_idem]
    rfl
  refine ⟨hpre, fun hdec hl => ?_, fun hdec hl => ?_, fun hdec => ?_⟩
  · subst hl
    rw [hw2 .pass 0 (n.getD false) (by
      simp only [nf_leaf]
      rw [hsym1, if_pos hdec]
      rfl), htape2]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _ |>.trans (moveInputPos_zero _)
    · rfl
    · funext i
      by_cases hi : i = 1
      · subst hi
        simp only [he₁, Function.update_self, SignType.coe_zero, add_zero]
        rfl
      · simp only [he₁, Function.update_of_ne hi]
    · rfl
  · subst hl
    -- the second block step, then the two head adjustments
    set m₂ : SignType := if mv = 1 then 1 else -1 with hm₂
    set m₃ : SignType := if mv = -1 then -1 else 0 with hm₃
    have h2 := hw2 (.adj₁ σ mv) m₂ (n.getD false) (by
      simp only [nf_leaf]
      rw [hsym1, if_pos hdec]
      rfl)
    rw [htape2] at h2
    set e₂ : Cfg 2 Bool (nf_LeafSt N) x := { e₁ with
        state := some (.adj₁ σ mv)
        inputPos := moveInputPos e₁.inputPos 0
        workTapes := Function.update e.workTapes 1 (nf_blockWrite (e.workTapes 1) b n)
        workTapePos := Function.update e₁.workTapePos 1 (e₁.workTapePos 1 + m₂) } with he₂
    have h3 : (nf_leaf N (some t)).runFrom e 3 = { e₂ with
        state := some (.adj₂ σ mv)
        inputPos := moveInputPos e₂.inputPos 0
        workTapePos := Function.update e₂.workTapePos 1 (e₂.workTapePos 1 + m₃) } := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step', h2,
        step_of_tapeAction_move (nf_leaf N (some t)) e₂ (q := .adj₁ σ mv) 1 0 m₃ rfl rfl]
    have h4 : (nf_leaf N (some t)).runFrom e 4 = { e₂ with
        state := some (.read σ)
        inputPos := moveInputPos (moveInputPos e₂.inputPos 0) 0
        workTapePos := Function.update (Function.update e₂.workTapePos 1 (e₂.workTapePos 1 + m₃)) 1
          (Function.update e₂.workTapePos 1 (e₂.workTapePos 1 + m₃) 1 + m₃) } := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, MultiTapeTM.runFrom_succ_eq_step', h3,
        step_of_tapeAction_move (nf_leaf N (some t)) _ (q := .adj₂ σ mv) 1 0 m₃ rfl rfl]
    refine ⟨fun u hu s hs => ?_, ?_⟩
    · rcases (by omega : u < 2 ∨ u = 2 ∨ u = 3) with hu2 | rfl | rfl
      · exact hpre u hu2 s hs
      · rw [h2] at hs
        cases hs
        rfl
      · rw [h3] at hs
        cases hs
        rfl
    · rw [h4]
      apply Cfg.ext
      · rfl
      · show moveInputPos (moveInputPos (moveInputPos (moveInputPos e.inputPos 0) 0) 0) 0 = _
        rw [moveInputPos_zero, moveInputPos_zero, moveInputPos_zero, moveInputPos_zero]
      · rfl
      · funext i
        by_cases hi : i = 1
        · subst hi
          simp only [he₂, he₁, Function.update_self]
          rw [hm₂, hm₃]
          rcases mv with _ | _ | _ <;> simp <;> ring
        · simp only [he₂, he₁, Function.update_of_ne hi]
      · rfl
  · have e2 : (nf_leaf N (some t)).runFrom e 2 =
        (nf_leaf N (some t)).step ((nf_leaf N (some t)).runFrom e 1) :=
      MultiTapeTM.runFrom_succ_eq_step'
    rw [e2, h1, step_of_tapeAction_move (nf_leaf N (some t)) e₁ (q := .blk₂ σ claim n mv last
        (e.workTapes 1 b)) (q' := .rej) 1 0 0 rfl (by
        simp only [nf_leaf]
        rw [hsym1, if_neg hdec])]

/-- **The read of one record by a work-tape instance.** From a record boundary, with the record on
tape `0` from its head, the instance for work tape `t` reads the record in `2k + 4` steps, at no
exit before. At a live control it is then at the first cell of the block on tape `1`, carrying
the decoded claim on tape `t`, the cell's new content under the recomputed action, the simulated
move and the end flag, with the head of tape `0` one cell past the record and nothing else
changed; at a halted control it rejects.

**Proof sketch.** Up to the record's last bit the leaf reads the record, and there the parser
completes it. The leaf's table at a live control is then a right move on tape `0` into the block's
first state, with the record's decoded claims and recomputed action. -/
private theorem nf_leaf_record_wk (N : FinNDTM Bool) (t : Fin N.k) {x : List Bool}
    (d : Cfg 2 Bool (nf_LeafSt N) x) (rec : Fin (2 * N.k + 4) → Bool) (ctl : nf_Control N)
    (hst : d.state = some (.read ((0, fun _ => none), ctl)))
    (hA : ∀ p : Fin (2 * N.k + 4), d.workTapes 0 (d.workTapePos 0 + (p.val : ℤ)) = some (rec p)) :
    (∀ u < 2 * N.k + 4, ∀ s, ((nf_leaf N (some t)).runFrom d u).state = some s →
      nf_leafExit N s = none) ∧
    (∀ q, ctl.1 = some q →
      (nf_leaf N (some t)).runFrom d (2 * N.k + 4) = { d with
        state := some (.blk₁ ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl)
          (nf_decode N.k (fun p => some (rec p)) t.succ)
          (((nf_act N (fun p => some (rec p)) q).workTapes t).1.getD
            (nf_decode N.k (fun p => some (rec p)) t.succ))
          ((nf_act N (fun p => some (rec p)) q).workTapes t).2 (rec ⟨2 * N.k + 3, by omega⟩))
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) }) ∧
    (ctl.1 = none → ((nf_leaf N (some t)).runFrom d (2 * N.k + 4)).state = some .rej) := by
  obtain ⟨hpre, σ, h1, h2, h3, h4, hrun, hsym⟩ := nf_leaf_toLast N (some t) d rec ctl hst hA
  refine ⟨hpre, ?_⟩
  set c : Cfg 2 Bool (nf_LeafSt N) x := { d with
      state := some (.read σ)
      workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 3 : ℕ)) }
    with hc
  refine ⟨fun q hq => ?_, fun hn => ?_⟩
  · rw [hrun, step_of_tapeAction_move (nf_leaf N (some t)) c (q := .read σ)
      (q' := .blk₁ ((0, fun _ => none), nf_complete N (fun p => some (rec p)) ctl)
        (nf_decode N.k (fun p => some (rec p)) t.succ)
        (((nf_act N (fun p => some (rec p)) q).workTapes t).1.getD
          (nf_decode N.k (fun p => some (rec p)) t.succ))
        ((nf_act N (fun p => some (rec p)) q).workTapes t).2 (rec ⟨2 * N.k + 3, by omega⟩))
      0 0 1 rfl (by
      simp only [nf_leaf]
      rw [if_pos h1, hsym, Option.getD_some, h3, h4, h2, hq])]
    apply Cfg.ext
    · rfl
    · exact moveInputPos_zero _
    · rfl
    · funext i
      by_cases hi : i = 0
      · subst hi
        simp only [hc, Function.update_self, SignType.coe_one]
        push_cast
        ring
      · simp only [hc, Function.update_of_ne hi]
    · rfl
  · rw [hrun, step_of_tapeAction_move (nf_leaf N (some t)) c (q := .read σ) (q' := .rej) 0 0 0 rfl
      (by
        simp only [nf_leaf]
        rw [if_pos h1, h2, hn])]

/-- **The block representation of a replayed work tape.** Tape `1` holds the replayed tape's cells
`[lo, hi]` as two-bit blocks from cell `p₀` (cell `y` at `p₀ + 2y` and `p₀ + 2y + 1`), with the
contents `v`, and is blank elsewhere; and `v` is blank outside `[lo, hi]`. -/
private def nf_blocks (B : ℤ → Option Bool) (p₀ lo hi : ℤ) (v : ℤ → Option Bool) : Prop :=
  (∀ y : ℤ, B (p₀ + 2 * y) = (if lo ≤ y ∧ y ≤ hi then some (v y).isSome else none) ∧
    B (p₀ + 2 * y + 1) = (if lo ≤ y ∧ y ≤ hi then some ((v y).getD false) else none)) ∧
  ∀ y : ℤ, ¬(lo ≤ y ∧ y ≤ hi) → v y = none

/-- A represented cell's block decodes to the cell's content, visited or not. -/
private theorem nf_blocks_decode {B : ℤ → Option Bool} {p₀ lo hi : ℤ} {v : ℤ → Option Bool}
    (h : nf_blocks B p₀ lo hi v) (y : ℤ) :
    nf_blockDecode (B (p₀ + 2 * y)) (B (p₀ + 2 * y + 1)) = v y := by
  rw [(h.1 y).1, (h.1 y).2]
  by_cases hy : lo ≤ y ∧ y ≤ hi
  · rw [if_pos hy, if_pos hy]
    unfold nf_blockDecode
    cases v y with
    | none => rfl
    | some b => rfl
  · rw [if_neg hy, if_neg hy, h.2 y hy]
    rfl

/-- Rewriting the block of a cell next to or inside the represented interval extends the
interval by that cell and updates its content.

**Proof sketch.** The rewritten cells are the block of `y`; every other cell is unchanged, and a
cell other than `y` is in the new interval exactly when it is in the old one, since `y` is at most
one cell outside it. -/
private theorem nf_blocks_write {B : ℤ → Option Bool} {p₀ lo hi : ℤ} {v : ℤ → Option Bool}
    (h : nf_blocks B p₀ lo hi v) (y : ℤ) (n : Option Bool) (h1 : lo - 1 ≤ y) (h2 : y ≤ hi + 1) :
    nf_blocks (nf_blockWrite B (p₀ + 2 * y) n) p₀ (min lo y) (max hi y)
      (Function.update v y n) := by
  have hin : ∀ z, z ≠ y → ((min lo y ≤ z ∧ z ≤ max hi y) ↔ (lo ≤ z ∧ z ≤ hi)) := by
    intro z hz
    constructor
    · rintro ⟨ha, hb⟩
      rw [min_le_iff] at ha
      rw [le_max_iff] at hb
      omega
    · rintro ⟨ha, hb⟩
      exact ⟨min_le_of_left_le ha, le_max_of_le_left hb⟩
  have hy : min lo y ≤ y ∧ y ≤ max hi y := ⟨min_le_right _ _, le_max_right _ _⟩
  refine ⟨fun z => ?_, fun z hz => ?_⟩
  · unfold nf_blockWrite
    by_cases hzy : z = y
    · rw [hzy]
      have e2 : p₀ + 2 * y ≠ p₀ + 2 * y + 1 := by omega
      rw [Function.update_of_ne e2]
      simp only [Function.update_self, if_pos hy, and_self]
    · have e1 : p₀ + 2 * z ≠ p₀ + 2 * y := by omega
      have e2 : p₀ + 2 * z ≠ p₀ + 2 * y + 1 := by omega
      have e3 : p₀ + 2 * z + 1 ≠ p₀ + 2 * y := by omega
      have e4 : p₀ + 2 * z + 1 ≠ p₀ + 2 * y + 1 := by omega
      rw [Function.update_of_ne e2, Function.update_of_ne e1, Function.update_of_ne e4,
        Function.update_of_ne e3, Function.update_of_ne hzy, (h.1 z).1, (h.1 z).2]
      by_cases hz' : lo ≤ z ∧ z ≤ hi
      · rw [if_pos hz', if_pos hz', if_pos ((hin z hzy).mpr hz'), if_pos ((hin z hzy).mpr hz')]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hz', if_neg hz', if_neg (fun h' => hz' ((hin z hzy).mp h')),
          if_neg (fun h' => hz' ((hin z hzy).mp h'))]
        exact ⟨rfl, rfl⟩
  · have hzy : z ≠ y := fun e => hz (e ▸ hy)
    rw [Function.update_of_ne hzy]
    exact h.2 z (fun h' => hz ((hin z hzy).mpr h'))

/-- The nonblank cells of a represented interval `[lo, hi]` are exactly its blocks'.

**Proof sketch.** Every cell is the first or the second cell of some block; a block's cells are
nonblank exactly when its cell is in the interval. -/
private theorem nf_blocks_support {B : ℤ → Option Bool} {p₀ lo hi : ℤ} {v : ℤ → Option Bool}
    (h : nf_blocks B p₀ lo hi v) (q : ℤ) :
    B q ≠ none ↔ p₀ + 2 * lo ≤ q ∧ q ≤ p₀ + 2 * hi + 1 := by
  obtain ⟨z, hz | hz⟩ : ∃ z, q = p₀ + 2 * z ∨ q = p₀ + 2 * z + 1 :=
    ⟨(q - p₀) / 2, by omega⟩
  · subst hz
    rw [(h.1 z).1]
    by_cases hzi : lo ≤ z ∧ z ≤ hi
    · rw [if_pos hzi]
      exact ⟨fun _ => by omega, fun _ => Option.some_ne_none _⟩
    · rw [if_neg hzi]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd ⟨by omega, by omega⟩ hzi⟩
  · subst hz
    rw [(h.1 z).2]
    by_cases hzi : lo ≤ z ∧ z ≤ hi
    · rw [if_pos hzi]
      exact ⟨fun _ => by omega, fun _ => Option.some_ne_none _⟩
    · rw [if_neg hzi]
      exact ⟨fun h' => absurd rfl h', fun h' => absurd ⟨by omega, by omega⟩ hzi⟩

/-- A simulated move is at most one cell. -/
private theorem nf_signType_bound (m : SignType) : -1 ≤ (m : ℤ) ∧ (m : ℤ) ≤ 1 := by
  rcases m with _ | _ | _ <;> simp

/-- **A work tape's replay.** From a record boundary with a stream of `n ≥ 1` records on tape `0`
from its head (only the last end-flagged), at a control that follows the virtual configuration
`c`, and with tape `1` holding `c`'s work tape `t` as blocks from `p₀` over an interval
`[lo, hi]` within one cell of `c`'s head (and the head of tape `1` on the head's block), the
instance for work tape `t` reaches an exit at some time `T`, at no exit before. It passes exactly
when every record's claim on tape `t` is checked along the decoded virtual run; then
`T + 2 = (2k + 8)n`, its head on tape `0` is one cell past the stream, and tape `1` is blank
outside a nonempty contiguous region of nonblank cells `[p₀ + 2lo', p₀ + 2hi' + 1]`, of at most
`hi - lo + 1 + n` blocks, holding the head of tape `1` on its block `y`'s second cell. Otherwise it
rejects.

**Proof sketch.** Induct over the records. One record is its read, then its block: a dead control
rejects after the read, a failed check rejects after the block's second step. A passed check
writes the block of the virtual head with the cell's new content, which is the virtual step's,
so the block representation extends by that cell; after the end-flagged record the leaf passes
there, and after any other the head of tape `1` moves to the next virtual head's block, within one
cell of the extended interval, where the induction hypothesis applies. -/
private theorem nf_leaf_run_wk (N : FinNDTM Bool) (t : Fin N.k) {x : List Bool} (p₀ : ℤ) :
    ∀ (rs : List (Fin (2 * N.k + 4) → Bool)) (d : Cfg 2 Bool (nf_LeafSt N) x)
      (ctl : nf_Control N) (c : Cfg N.k Bool N.State x) (lo hi : ℤ),
    rs ≠ [] →
    (∀ r (h : r < rs.length), rs[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = rs.length)) →
    d.state = some (.read ((0, fun _ => none), ctl)) → ctl.1 = c.state →
    nf_blocks (d.workTapes 1) p₀ lo hi (c.workTapes t) →
    d.workTapePos 1 = p₀ + 2 * c.workTapePos t →
    lo ≤ hi + 1 → lo - 1 ≤ c.workTapePos t → c.workTapePos t ≤ hi + 1 →
    (∀ p : ℕ, p < (rs.flatMap List.ofFn).length →
      d.workTapes 0 (d.workTapePos 0 + p) = (rs.flatMap List.ofFn)[p]?) →
    ∃ T, (∀ u < T, ∀ s, ((nf_leaf N (some t)).runFrom d u).state = some s →
        nf_leafExit N s = none) ∧
      ((∀ r (h : r < rs.length), nf_ok N ((rs.take r).foldl (nf_vstep N) c) rs[r] t.succ) →
        T + 2 = (2 * N.k + 8) * rs.length ∧
        ∃ (B : ℤ → Option Bool) (lo' hi' y : ℤ),
          (nf_leaf N (some t)).runFrom d T = { d with
            state := some .pass
            workTapes := Function.update d.workTapes 1 B
            workTapePos := Function.update (Function.update d.workTapePos 0
              (d.workTapePos 0 + ((2 * N.k + 4) * rs.length : ℕ))) 1 (p₀ + 2 * y + 1) } ∧
          (∀ q, B q ≠ none ↔ p₀ + 2 * lo' ≤ q ∧ q ≤ p₀ + 2 * hi' + 1) ∧
          lo' ≤ y ∧ y ≤ hi' ∧ hi' - lo' ≤ hi - lo + rs.length) ∧
      (¬ (∀ r (h : r < rs.length), nf_ok N ((rs.take r).foldl (nf_vstep N) c) rs[r] t.succ) →
        ((nf_leaf N (some t)).runFrom d T).state = some .rej)
  | [], _, _, _, _, _, hne, _, _, _, _, _, _, _, _, _ => absurd rfl hne
  | rec :: rs, d, ctl, c, lo, hi, _, hflag, hst, hc, hB, hpos, h0, h1, h2, hA => by
    obtain ⟨hA0, hA1⟩ := nf_stream_cons N.k rec rs (d.workTapes 0) (d.workTapePos 0) hA
    obtain ⟨hpreR, hlive, hdead⟩ := nf_leaf_record_wk N t d rec ctl hst hA0
    have hall := nf_all_cons N c rec rs (fun c rec => nf_ok N c rec t.succ)
    obtain ⟨hfl, hflag'⟩ := nf_flags_cons rec rs hflag
    by_cases hlv : c.state = none
    · refine ⟨2 * N.k + 4, hpreR, fun h => absurd hlv (hall.mp h).1.1,
        fun _ => hdead (hc.trans hlv)⟩
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hlv
    have hrun := hlive q (hc.trans hq)
    set r : Fin (2 * N.k + 4) → Option Bool := fun p => some (rec p) with hr
    set a := nf_act N r q with ha
    set claim := nf_decode N.k r t.succ with hclaim
    set n := (a.workTapes t).1.getD claim with hn
    set e : Cfg 2 Bool (nf_LeafSt N) x := { d with
        state := some (.blk₁ ((0, fun _ => none), nf_complete N r ctl) claim n (a.workTapes t).2
          (rec ⟨2 * N.k + 3, by omega⟩))
        workTapePos := Function.update d.workTapePos 0 (d.workTapePos 0 + (2 * N.k + 4 : ℕ)) }
      with he
    obtain ⟨hpreB, hpassL, hpassN, hrejB⟩ := nf_leaf_block N t e _ claim n (a.workTapes t).2
      (rec ⟨2 * N.k + 3, by omega⟩) rfl
    have hew1 : e.workTapes 1 = d.workTapes 1 := rfl
    have hep1 : e.workTapePos 1 = d.workTapePos 1 := by
      simp only [he]
      exact Function.update_of_ne (by decide) _ _
    have hdecB : nf_blockDecode (e.workTapes 1 (e.workTapePos 1))
        (e.workTapes 1 (e.workTapePos 1 + 1)) = c.workTapeSymbols t := by
      rw [hew1, hep1, hpos, Cfg.workTapeSymbols_eq]
      exact nf_blocks_decode hB _
    have hpre2 : ∀ u < 2 * N.k + 4 + 2, ∀ s, ((nf_leaf N (some t)).runFrom d u).state = some s →
        nf_leafExit N s = none := by
      intro u hu s hs
      by_cases hu1 : u < 2 * N.k + 4
      · exact hpreR u hu1 s hs
      · obtain ⟨v, rfl⟩ : ∃ v, u = (2 * N.k + 4) + v := ⟨u - (2 * N.k + 4), by omega⟩
        rw [MultiTapeTM.runFrom_add, hrun] at hs
        exact hpreB v (by omega) s hs
    by_cases hok0 : claim = c.workTapeSymbols t
    · have hdec : nf_blockDecode (e.workTapes 1 (e.workTapePos 1))
          (e.workTapes 1 (e.workTapePos 1 + 1)) = claim := hdecB.trans hok0.symm
      have hok : nf_ok N c rec t.succ := ⟨hlv, hok0⟩
      -- the virtual step on work tape `t`
      have hvt : (nf_vstep N c rec).workTapes t = Function.update (c.workTapes t)
          (c.workTapePos t) n := by
        simp only [nf_vstep, hq]
        rw [Action.apply_workTapes, ← hok0]
      have hvp : (nf_vstep N c rec).workTapePos t = c.workTapePos t + (a.workTapes t).2 := by
        simp only [nf_vstep, hq]
        rw [Action.apply_workTapePos]
      have hBw : nf_blocks (nf_blockWrite (d.workTapes 1) (p₀ + 2 * c.workTapePos t) n) p₀
          (min lo (c.workTapePos t)) (max hi (c.workTapePos t))
          ((nf_vstep N c rec).workTapes t) := by
        rw [hvt]
        exact nf_blocks_write hB _ n h1 h2
      have hmv := nf_signType_bound (a.workTapes t).2
      cases rs with
      | nil =>
        have hl : rec ⟨2 * N.k + 3, by omega⟩ = true := by simpa using hfl
        have h2s := hpassL hdec hl
        refine ⟨2 * N.k + 4 + 2, hpre2, fun _ => ⟨by simp only [List.length_singleton]; omega,
          nf_blockWrite (d.workTapes 1) (p₀ + 2 * c.workTapePos t) n,
          min lo (c.workTapePos t), max hi (c.workTapePos t), c.workTapePos t, ?_,
          nf_blocks_support hBw, min_le_right _ _, le_max_right _ _, by simp; omega⟩,
          fun hn' => absurd (hall.mpr ⟨hok, fun r hr => by simp at hr⟩) hn'⟩
        rw [MultiTapeTM.runFrom_add, hrun, h2s]
        apply Cfg.ext
        · rfl
        · rfl
        · show Function.update d.workTapes 1 (nf_blockWrite (e.workTapes 1) (e.workTapePos 1) n) = _
          rw [hew1, hep1, hpos]
        · funext i
          by_cases hi : i = 1
          · subst hi
            simp only [Function.update_self]
            rw [hep1, hpos]
          · simp only [he, Function.update_of_ne hi, List.length_singleton, Nat.mul_one]
        · rfl
      | cons rec' rs' =>
        have hl : rec ⟨2 * N.k + 3, by omega⟩ = false := by simpa using hfl
        obtain ⟨hpre4, h4s⟩ := hpassN hdec hl
        set d' : Cfg 2 Bool (nf_LeafSt N) x := { e with
            state := some (.read ((0, fun _ => none), nf_complete N r ctl))
            workTapes := Function.update e.workTapes 1
              (nf_blockWrite (e.workTapes 1) (e.workTapePos 1) n)
            workTapePos := Function.update e.workTapePos 1
              (e.workTapePos 1 + 2 * ((a.workTapes t).2 : ℤ)) } with hd'
        have hvc := nf_vstep_state N c ctl rec hc
        have hB' : nf_blocks (d'.workTapes 1) p₀ (min lo (c.workTapePos t))
            (max hi (c.workTapePos t)) ((nf_vstep N c rec).workTapes t) := by
          show nf_blocks (Function.update e.workTapes 1
            (nf_blockWrite (e.workTapes 1) (e.workTapePos 1) n) 1) _ _ _ _
          rw [Function.update_self, hew1, hep1, hpos]
          exact hBw
        have hpos' : d'.workTapePos 1 = p₀ + 2 * (nf_vstep N c rec).workTapePos t := by
          show Function.update e.workTapePos 1 (e.workTapePos 1 + 2 * ((a.workTapes t).2 : ℤ)) 1 = _
          rw [Function.update_self, hep1, hpos, hvp]
          ring
        have hA' : ∀ p : ℕ, p < ((rec' :: rs').flatMap List.ofFn).length →
            d'.workTapes 0 (d'.workTapePos 0 + p) = ((rec' :: rs').flatMap List.ofFn)[p]? := by
          intro p hp
          have hw0 : d'.workTapes 0 = d.workTapes 0 := by
            simp only [hd', he]
            exact Function.update_of_ne (by decide) _ _
          have hp0 : d'.workTapePos 0 = d.workTapePos 0 + (2 * N.k + 4 : ℕ) := by
            simp only [hd', he]
            rw [Function.update_of_ne (by decide), Function.update_self]
          rw [hw0, hp0]
          exact hA1 p hp
        obtain ⟨T', hpre', hpass', hrej'⟩ := nf_leaf_run_wk N t p₀ (rec' :: rs') d'
          (nf_complete N r ctl) (nf_vstep N c rec) (min lo (c.workTapePos t))
          (max hi (c.workTapePos t)) (by simp) hflag' rfl hvc hB' hpos'
          (by have := min_le_right lo (c.workTapePos t); have := le_max_right hi (c.workTapePos t)
              omega)
          (by rw [hvp]; have := min_le_right lo (c.workTapePos t); omega)
          (by rw [hvp]; have := le_max_right hi (c.workTapePos t); omega) hA'
        have hrun4 : (nf_leaf N (some t)).runFrom d (2 * N.k + 4 + 4) = d' := by
          rw [MultiTapeTM.runFrom_add, hrun, h4s]
        refine ⟨2 * N.k + 4 + 4 + T', fun u hu s hs => ?_, fun h => ?_, fun h => ?_⟩
        · by_cases hu1 : u < 2 * N.k + 4
          · exact hpreR u hu1 s hs
          · by_cases hu2 : u < 2 * N.k + 4 + 4
            · obtain ⟨v, rfl⟩ : ∃ v, u = (2 * N.k + 4) + v := ⟨u - (2 * N.k + 4), by omega⟩
              rw [MultiTapeTM.runFrom_add, hrun] at hs
              exact hpre4 v (by omega) s hs
            · obtain ⟨v, rfl⟩ : ∃ v, u = (2 * N.k + 4 + 4) + v :=
                ⟨u - (2 * N.k + 4 + 4), by omega⟩
              rw [MultiTapeTM.runFrom_add, hrun4] at hs
              exact hpre' v (by omega) s hs
        · obtain ⟨hT, B, lo', hi', y, hcfg, hsupp, hy1, hy2, hsz⟩ := hpass' (hall.mp h).2
          refine ⟨by simp only [List.length_cons] at hT ⊢; rw [Nat.mul_add, ← hT]; ring, B, lo',
            hi', y, ?_, hsupp, hy1, hy2, ?_⟩
          · rw [MultiTapeTM.runFrom_add, hrun4, hcfg]
            apply Cfg.ext
            · rfl
            · rfl
            · show Function.update (Function.update d.workTapes 1 _) 1 B = _
              rw [Function.update_idem]
            · funext i
              by_cases hi : i = 1
              · subst hi
                simp only [Function.update_self]
              · have hi0 : i = 0 := by omega
                subst hi0
                simp only [hd', he, Function.update_self,
                  Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide), List.length_cons]
                push_cast
                ring
            · rfl
          · simp only [List.length_cons] at hsz ⊢
            have := min_le_left lo (c.workTapePos t)
            have := le_max_left hi (c.workTapePos t)
            rw [min_le_iff] at *
            rw [le_max_iff] at *
            push_cast at hsz ⊢
            have := min_le_right lo (c.workTapePos t)
            have := le_max_right hi (c.workTapePos t)
            omega
        · have hn' : ¬ ∀ r (h : r < (rec' :: rs').length),
              nf_ok N (((rec' :: rs').take r).foldl (nf_vstep N) (nf_vstep N c rec))
                (rec' :: rs')[r] t.succ := fun h' => h (hall.mpr ⟨hok, h'⟩)
          rw [MultiTapeTM.runFrom_add, hrun4]
          exact hrej' hn'
    · have hnok : ¬ nf_ok N c rec t.succ := fun h => hok0 h.2
      refine ⟨2 * N.k + 4 + 2, hpre2, fun h => absurd (hall.mp h).1 hnok, fun _ => ?_⟩
      rw [MultiTapeTM.runFrom_add, hrun]
      exact hrejB (fun h => hok0 (h.symm.trans hdecB))

/-- **The exit invariant on tape `1` gives its clear's input.** If tape `1`'s nonblank cells are
exactly the interval `[S, E]` and its head is at `h ∈ [S, E]`, then from `h - i` (with
`i = h - S`) it holds a blank-delimited word `R` of length `E - S + 1`, and blanking `R`'s cells
leaves tape `1` blank everywhere.

**Proof sketch.** Read `R` off the interval's cells. Inside the interval every cell is nonblank,
so it is `R`'s letter there; the cells just left and right of the interval are blank, as is the
buffer of `R` there; and every cell outside the interval was blank already. -/
private theorem nf_region (B : ℤ → Option Bool) (S E h : ℤ)
    (hB : ∀ q, B q ≠ none ↔ S ≤ q ∧ q ≤ E) (hS : S ≤ h) (hE : h ≤ E) :
    ∃ (R : List Bool) (i : ℕ), i ≤ R.length ∧ (R.length : ℤ) = E - S + 1 ∧ (i : ℤ) = h - S ∧
      (∀ p : ℤ, -1 ≤ p → p ≤ (R.length : ℤ) → B (h - i + p) = FinTM.bufferTape R p) ∧
      ∀ q, (if h - i ≤ q ∧ q < h - i + R.length then none else B q) = none := by
  set L : ℕ := (E - S + 1).toNat with hL
  have hL' : (L : ℤ) = E - S + 1 := by rw [hL]; omega
  refine ⟨List.ofFn fun m : Fin L => (B (S + m)).getD false, (h - S).toNat,
    by rw [List.length_ofFn]; omega, by rw [List.length_ofFn]; exact hL', by omega,
    fun p hp1 hp2 => ?_, fun q => ?_⟩
  · rw [List.length_ofFn] at hp2
    have hs : h - ((h - S).toNat : ℤ) = S := by omega
    rw [hs]
    by_cases hp0 : p = -1
    · subst hp0
      rw [FinTM.bufferTape_left]
      by_contra hne
      have := (hB _).mp hne
      omega
    · by_cases hpL : p = L
      · rw [hpL, FinTM.bufferTape_eq_none_of_not_mem]
        · by_contra hne
          have := (hB _).mp hne
          omega
        · rw [List.length_ofFn]
          omega
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = m := ⟨p.toNat, by omega⟩
        have hm : m < L := by omega
        rw [FinTM.bufferTape_nat, List.getElem?_ofFn]
        simp only [hm, dite_true]
        have hne : B (S + m) ≠ none := (hB _).mpr ⟨by omega, by omega⟩
        obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hne
        rw [hb]
        rfl
  · rw [List.length_ofFn]
    by_cases hq : h - ((h - S).toNat : ℤ) ≤ q ∧ q < h - ((h - S).toNat : ℤ) + L
    · rw [if_pos hq]
    · rw [if_neg hq]
      by_contra hne
      have := (hB q).mp hne
      omega

/-! ### The verifier's characterization -/

/-- A stream of records has `2k + 4` cells per record. -/
private theorem nf_stream_length (k : ℕ) (rs : List (Fin (2 * k + 4) → Bool)) :
    (rs.flatMap List.ofFn).length = (2 * k + 4) * rs.length := by
  rw [length_flatMap_uniform rs List.ofFn (fun _ => List.length_ofFn), Nat.mul_comm]

/-- The entry of the verifier's phases for work tape `m`: its replay, or the passing verdict once
every work tape has been replayed. -/
private def nf_tapeEntry (N : FinNDTM Bool) {SL : Type}
    (L : Option (Fin N.k) → MultiTapeTM 2 Bool SL) (m : ℕ) : Σ i, nf_St N SL i :=
  if h : m < N.k then ⟨.rep (some ⟨m, h⟩), (L (some ⟨m, h⟩)).q₀⟩ else ⟨.park, true⟩

/-- Every check of the verifier passes on a stream of records: the control sweep's, and every
record's claim on every replayed tape along the decoded virtual run from `N`'s start. -/
private def nf_allPass (N : FinNDTM Bool) (x : List Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) : Prop :=
  nf_sweepPass N ((rs.flatMap List.ofFn).foldl (nf_sweepStep N) (nf_sweepInit N)) = true ∧
    ∀ (i : Fin (N.k + 1)) (r : ℕ) (h : r < rs.length),
      nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] i

/-- **The verifier over the work tapes from `m` on.** From the entry of work tape `m`, with tape
`0` holding the stream from cell `0` and its head there, tape `1` blank and the output empty, the
verifier reaches a first verdict at some time `T`. It accepts exactly when every record's claim
on every work tape `t ≥ m` is checked along the decoded virtual run; then the output is empty and
`T ≤ (k - m)((2(2k + 4) + 12)n + 15)`.

**Proof sketch.** Induct on `k - m`. With every work tape replayed the entry is the passing
verdict. Otherwise run the replay of tape `m` from tape `1`'s head: a failed check rejects one
dispatch later; a pass is followed by the return of tape `0` and the clear of tape `1`, which the
exit invariant feeds and which leaves tape `1` blank again, at the next work tape's entry, where
the induction hypothesis applies. Inside each phase the verifier is at no verdict. The time adds
the replay's `(2k + 8)n - 2`, the dispatches, the return's `|s| + 6` and the clear's at most
`4|R| + 9` with `|R| ≤ 2n`. -/
private theorem nf_V_tail (N : FinNDTM Bool) {x : List Bool}
    (rs : List (Fin (2 * N.k + 4) → Bool)) (hne : rs ≠ [])
    (hflag : ∀ r (h : r < rs.length), rs[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = rs.length)) :
    ∀ (d m : ℕ), m + d = N.k → ∀ {S : Type} (c : Cfg 2 Bool S x), c.state.isSome →
      c.workTapes 0 = FinTM.bufferTape (rs.flatMap List.ofFn) → c.workTapePos 0 = 0 →
      c.workTapes 1 = (fun _ => none) → c.output = [] →
      ∃ T, (((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
            (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) T).state = some ⟨.park, true⟩ ∨
          ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
            (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) T).state =
              some ⟨.park, false⟩) ∧
        (∀ u < T, ∀ b, ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) u).state ≠ some ⟨.park, b⟩) ∧
        (((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
            (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) T).state = some ⟨.park, true⟩ ↔
          ∀ (t : Fin N.k), m ≤ t.val → ∀ (r : ℕ) (h : r < rs.length),
            nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] t.succ) ∧
        ((∀ (t : Fin N.k), m ≤ t.val → ∀ (r : ℕ) (h : r < rs.length),
            nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] t.succ) →
          ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
            (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) T).output = [] ∧
          T ≤ d * ((2 * (2 * N.k + 4) + 12) * rs.length + 15))
  | 0, m, hm, S, c, hcs, _, _, _, hout => by
    have hk : ¬ m < N.k := by omega
    have he : nf_tapeEntry N (nf_leaf N) m = ⟨.park, true⟩ := by
      unfold nf_tapeEntry
      rw [dif_neg hk]
    have hst : (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)).state = some ⟨.park, true⟩ := by
      rw [Cfg.mapState_state, he]
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hcs
      rw [hq]
      rfl
    refine ⟨0, Or.inl (by rw [MultiTapeTM.runFrom_zero]; exact hst), fun u hu => absurd hu
      (Nat.not_lt_zero u), ⟨fun _ t ht => absurd t.isLt (by omega),
      fun _ => by rw [MultiTapeTM.runFrom_zero]; exact hst⟩, fun _ => ⟨?_, Nat.zero_le _⟩⟩
    rw [MultiTapeTM.runFrom_zero, Cfg.mapState_output, hout]
  | d + 1, m, hm, S, c, hcs, hA, hA0, hB, hout => by
    have hk : m < N.k := by omega
    set t : Fin N.k := ⟨m, hk⟩ with ht
    set s := rs.flatMap List.ofFn with hs
    have hslen : s.length = (2 * N.k + 4) * rs.length := nf_stream_length N.k rs
    have he : nf_tapeEntry N (nf_leaf N) m =
        ⟨.rep (some t), (nf_leaf N (some t)).q₀⟩ := by
      unfold nf_tapeEntry
      rw [dif_pos hk]
    -- the replay of work tape `m`, from tape `1`'s head
    have hre := nf_retag (N := N) (SL := nf_LeafSt N) c (nf_Ph.rep (some t))
      (nf_leaf N (some t)).q₀ hcs
    set dL : Cfg 2 Bool (nf_LeafSt N) x :=
      { state := some (nf_leaf N (some t)).q₀, inputPos := c.inputPos, workTapes := c.workTapes,
        workTapePos := c.workTapePos, output := c.output } with hdL
    have hinit_state : (N.tm.initCfg x).state = some N.tm.q₀ := by
      rw [NDTM.initCfg_eq, Cfg.init_state]
    have hinit_tape : (N.tm.initCfg x).workTapes t = fun _ => none := by
      funext p
      rw [NDTM.initCfg_eq, Cfg.init_workTapes]
    have hinit_pos : (N.tm.initCfg x).workTapePos t = 0 := by
      rw [NDTM.initCfg_eq, Cfg.init_workTapePos]
    have hblk0 : nf_blocks (dL.workTapes 1) (c.workTapePos 1) 0 (-1)
        ((N.tm.initCfg x).workTapes t) := by
      show nf_blocks (c.workTapes 1) _ _ _ _
      rw [hB, hinit_tape]
      refine ⟨fun y => ?_, fun y _ => rfl⟩
      rw [if_neg (by omega), if_neg (by omega)]
      exact ⟨rfl, rfl⟩
    obtain ⟨T₁, hpre₁, hpass₁, hrej₁⟩ := nf_leaf_run_wk N t (c.workTapePos 1) rs dL
      (some N.tm.q₀, none, false) (N.tm.initCfg x) 0 (-1) hne hflag rfl hinit_state.symm hblk0
      (by show c.workTapePos 1 = _; rw [hinit_pos]; ring) (by omega) (by rw [hinit_pos]; omega)
      (by rw [hinit_pos]; omega) (by
        intro p hp
        show c.workTapes 0 (c.workTapePos 0 + p) = _
        rw [hA, hA0, zero_add, FinTM.bufferTape_nat])
    have hguard₁ : ∀ u < T₁, ∀ q, ((nf_M N (nf_leaf N) (nf_Ph.rep (some t))).runFrom dL u).state =
        some q → nf_red N (nf_leaf N) (nf_leafExit N) (nf_Ph.rep (some t)) q = none := by
      intro u hu q hq
      have h := hpre₁ u hu q hq
      show (match nf_leafExit N q with
        | some true => _ | some false => _ | none => none) = none
      rw [h]
    have hwin₁ : ∀ u ≤ T₁, ∀ b, ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
        (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) u).state ≠ some ⟨.park, b⟩ := by
      intro u hu b
      rw [he, hre]
      unfold nf_V
      rw [phaseHostTM_run_le (nf_M N (nf_leaf N)) _ (nf_red N (nf_leaf N) (nf_leafExit N))
        (nf_Ph.rep (some t)) dL T₁ hguard₁ u hu]
      exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
    by_cases hok : ∀ r (h : r < rs.length),
        nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] t.succ
    · obtain ⟨hT₁, B, lo', hi', y, hcfg, hsupp, hy1, hy2, hsz⟩ := hpass₁ hok
      set p₁ := c.workTapePos 1 with hp₁
      -- the replay passes: one dispatch to the return of tape `0`
      set c₁ : Cfg 2 Bool (nf_LeafSt N) x := { dL with
          state := some .pass
          workTapes := Function.update dL.workTapes 1 B
          workTapePos := Function.update (Function.update dL.workTapePos 0
            (dL.workTapePos 0 + ((2 * N.k + 4) * rs.length : ℕ))) 1 (p₁ + 2 * y + 1) } with hc₁
      obtain ⟨-, hR⟩ := phaseHostTM_run (nf_M N (nf_leaf N)) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
        (nf_red N (nf_leaf N) (nf_leafExit N)) (nf_Ph.rep (some t)) dL c₁ T₁ hcfg
        nf_LeafSt.pass rfl ⟨.aFwd (some t), .run⟩ rfl hguard₁
      have hre1 := nf_retag (N := N) (SL := nf_LeafSt N)
        (S := nf_St N (nf_LeafSt N) (nf_Ph.rep (some t))) c₁ (nf_Ph.aFwd (some t)) SeekPhase.run
        (by rw [hc₁]; rfl)
      set c₁' : Cfg 2 Bool SeekPhase x :=
        { state := some .run, inputPos := c₁.inputPos, workTapes := c₁.workTapes,
          workTapePos := c₁.workTapePos, output := c₁.output } with hc₁'
      have hA1 : c₁'.workTapePos 0 = s.length := by
        simp only [hc₁', hc₁, hdL]
        rw [Function.update_of_ne (by decide), Function.update_self, hA0, zero_add, hslen]
      have htape1 : ∀ p, c₁'.workTapes 0 p = FinTM.bufferTape s p := by
        intro p
        simp only [hc₁', hc₁, hdL]
        rw [Function.update_of_ne (by decide), hA]
      obtain ⟨c₃, h3, h3s, h3p0, h3p1, h3w, h3i, h3o, h3win⟩ := nf_aReturn N (nf_leaf N)
        (nf_leafExit N) (some t) s c₁' rfl hA1 htape1
      have h3' : (nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          ((c₁' : Cfg 2 Bool (nf_St N (nf_LeafSt N) (nf_Ph.aFwd (some t))) x).mapState
            (Sigma.mk (nf_Ph.aFwd (some t)))) (s.length + 6) =
          c₃.mapState (fun _ => (⟨nf_Ph.bFwd t, SeekPhase.run⟩ :
            Σ i, nf_St N (nf_LeafSt N) i)) := h3
      have hre3 := nf_retag (N := N) (SL := nf_LeafSt N) (S := SeekPhase) c₃ (nf_Ph.bFwd t)
        SeekPhase.run h3s
      set c₃' : Cfg 2 Bool SeekPhase x :=
        { state := some .run, inputPos := c₃.inputPos, workTapes := c₃.workTapes,
          workTapePos := c₃.workTapePos, output := c₃.output } with hc₃'
      have hB3 : c₃'.workTapes 1 = B := by
        simp only [hc₃']
        rw [h3w]
        simp only [hc₁', hc₁]
        rw [Function.update_self]
      have hP3 : c₃'.workTapePos 1 = p₁ + 2 * y + 1 := by
        simp only [hc₃']
        rw [h3p1]
        simp only [hc₁', hc₁]
        rw [Function.update_self]
      -- the region of tape `1`, and its clear
      obtain ⟨R, i, hiR, hRlen, hieq, hRt, hclr⟩ := nf_region B (p₁ + 2 * lo') (p₁ + 2 * hi' + 1)
        (p₁ + 2 * y + 1) hsupp (by omega) (by omega)
      obtain ⟨c₅, h5, h5s, h5p1, h5p0, h5w0, h5i, h5o, h5w1, h5win⟩ := nf_bClear N (nf_leaf N)
        (nf_leafExit N) t R i hiR c₃' rfl (by
          intro p hp1 hp2
          rw [hB3, hP3]
          exact hRt p hp1 hp2)
      have h5' : (nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          ((c₃' : Cfg 2 Bool (nf_St N (nf_LeafSt N) (nf_Ph.bFwd t)) x).mapState
            (Sigma.mk (nf_Ph.bFwd t)))
          ((R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1)) =
          c₅.mapState (fun _ => nf_tapeEntry N (nf_leaf N) (m + 1)) := h5
      have hc5A : c₅.workTapes 0 = FinTM.bufferTape s := by
        rw [h5w0]
        simp only [hc₃']
        rw [h3w]
        simp only [hc₁', hc₁, hdL]
        rw [Function.update_of_ne (by decide), hA]
      have hc5A0 : c₅.workTapePos 0 = 0 := by
        rw [h5p0]
        simp only [hc₃']
        exact h3p0
      have hc5B : c₅.workTapes 1 = fun _ => none := by
        funext q
        rw [h5w1 q, hB3, hP3]
        exact hclr q
      have hc5o : c₅.output = [] := by
        rw [h5o]
        simp only [hc₃']
        rw [h3o]
        simp only [hc₁', hc₁, hdL]
        exact hout
      obtain ⟨T₂, hv2, hf2, hacc2, hb2⟩ := nf_V_tail N rs hne hflag d (m + 1) (by omega) c₅ h5s
        hc5A hc5A0 hc5B hc5o
      -- the chain
      set TC := (R.length - i + 1 + 1) + (R.length + 3 + 1) + (2 * R.length + 2 + 1) with hTC
      have hrun1 : (nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) (T₁ + 1) =
          (c₁' : Cfg 2 Bool (nf_St N (nf_LeafSt N) (nf_Ph.aFwd (some t))) x).mapState
            (Sigma.mk (nf_Ph.aFwd (some t))) := by
        rw [he, hre]
        unfold nf_V
        rw [hR, hre1]
      have hrun2 : (nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) (T₁ + 1 + (s.length + 6)) =
          (c₃' : Cfg 2 Bool (nf_St N (nf_LeafSt N) (nf_Ph.bFwd t)) x).mapState
            (Sigma.mk (nf_Ph.bFwd t)) := by
        rw [MultiTapeTM.runFrom_add, hrun1, h3', hre3]
      have hrun3 : (nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) (T₁ + 1 + (s.length + 6) + TC) =
          c₅.mapState (fun _ => nf_tapeEntry N (nf_leaf N) (m + 1)) := by
        rw [MultiTapeTM.runFrom_add, hrun2, h5']
      have hall : (∀ (t' : Fin N.k), m ≤ t'.val → ∀ (r : ℕ) (h : r < rs.length),
            nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] t'.succ) ↔
          (∀ (t' : Fin N.k), m + 1 ≤ t'.val → ∀ (r : ℕ) (h : r < rs.length),
            nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] t'.succ) := by
        constructor
        · exact fun h t' ht' => h t' (by omega)
        · intro h t' ht'
          by_cases he' : t'.val = m
          · have : t' = t := Fin.ext he'
            subst this
            exact hok
          · exact h t' (by omega)
      refine ⟨T₁ + 1 + (s.length + 6) + TC + T₂, ?_, fun u hu b => ?_, ?_, fun h => ?_⟩
      · rw [MultiTapeTM.runFrom_add, hrun3]
        exact hv2
      · by_cases hu1 : u ≤ T₁
        · exact hwin₁ u hu1 b
        obtain ⟨v, rfl⟩ : ∃ v, u = (T₁ + 1) + v := ⟨u - (T₁ + 1), by omega⟩
        rw [MultiTapeTM.runFrom_add, hrun1]
        by_cases hv1 : v < s.length + 6
        · exact h3win v hv1 b
        obtain ⟨w, rfl⟩ : ∃ w, v = (s.length + 6) + w := ⟨v - (s.length + 6), by omega⟩
        rw [MultiTapeTM.runFrom_add, h3', hre3]
        by_cases hw1 : w < TC
        · exact h5win w hw1 b
        obtain ⟨z, rfl⟩ : ∃ z, w = TC + z := ⟨w - TC, by omega⟩
        rw [MultiTapeTM.runFrom_add, h5']
        exact hf2 z (by omega) b
      · rw [MultiTapeTM.runFrom_add, hrun3, hacc2]
        exact hall.symm
      · obtain ⟨ho, hT₂⟩ := hb2 (hall.mp h)
        refine ⟨by rw [MultiTapeTM.runFrom_add, hrun3]; exact ho, ?_⟩
        have hRle : R.length ≤ 2 * rs.length := by omega
        have e1 : (2 * N.k + 8) * rs.length = 2 * (N.k * rs.length) + 8 * rs.length := by ring
        have e2 : (2 * N.k + 4) * rs.length = 2 * (N.k * rs.length) + 4 * rs.length := by ring
        have e3 : (d + 1) * ((2 * (2 * N.k + 4) + 12) * rs.length + 15) =
            d * ((2 * (2 * N.k + 4) + 12) * rs.length + 15) +
              (4 * (N.k * rs.length) + 20 * rs.length + 15) := by ring
        rw [e3]
        rw [e1] at hT₁
        rw [e2] at hslen
        omega
    · -- a failed check rejects one dispatch after the replay's exit
      have hrj := hrej₁ hok
      obtain ⟨-, hR⟩ := phaseHostTM_run (nf_M N (nf_leaf N)) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
        (nf_red N (nf_leaf N) (nf_leafExit N)) (nf_Ph.rep (some t)) dL _ T₁ rfl
        nf_LeafSt.rej hrj ⟨.park, false⟩ rfl hguard₁
      have hver : ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom
          (c.mapState (fun _ => nf_tapeEntry N (nf_leaf N) m)) (T₁ + 1)).state =
            some ⟨.park, false⟩ := by
        rw [he, hre]
        unfold nf_V
        rw [hR, Cfg.mapState_state, hrj]
        rfl
      refine ⟨T₁ + 1, Or.inr hver, fun u hu b => hwin₁ u (by omega) b,
        ⟨fun h => ?_, fun h => absurd (h t le_rfl) hok⟩, fun h => absurd (h t le_rfl) hok⟩
      rw [hver] at h
      exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).2 (by simp)

/-- Every check passes exactly when the control sweep passes, every input claim is checked, and
every work-tape claim is checked. -/
private theorem nf_allPass_iff (N : FinNDTM Bool) (x : List Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) :
    nf_allPass N x rs ↔
      nf_sweepPass N ((rs.flatMap List.ofFn).foldl (nf_sweepStep N) (nf_sweepInit N)) = true ∧
      (∀ (r : ℕ) (h : r < rs.length),
        nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] 0) ∧
      ∀ (t : Fin N.k), 0 ≤ t.val → ∀ (r : ℕ) (h : r < rs.length),
        nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] t.succ := by
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, h 0, fun t _ => h t.succ⟩
  · rintro ⟨hc, h0, ht⟩
    exact ⟨hc, fun i => Fin.cases h0 (fun t => ht t (Nat.zero_le _)) i⟩

/-- **The verifier's characterization.** From the stream start of a stream of `n ≥ 1` records
(only the last end-flagged), the verifier reaches a first verdict, `acc` or `rej`, at some time
`TQ`. It accepts exactly when every check passes (`nf_allPass`); then its output is empty and
`TQ ≤ 4|s| + 10 + k((2(2k + 4) + 12)n + 15)`.

**Proof sketch.** The control sweep is the scan fold, `2|s| + 2` steps, and a failed sweep
rejects at the dispatch. Otherwise the input's replay runs from the stream start: a failed check
rejects at its dispatch, a pass is followed by the return of tape `0` to the first work tape's
entry, with tape `0` holding the stream, its head at `0`, tape `1` blank and the output empty.
The work tapes' part is `nf_V_tail` from there. -/
private theorem nf_V_char (N : FinNDTM Bool) (x : List Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) (hne : rs ≠ [])
    (hflag : ∀ r (h : r < rs.length), rs[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = rs.length)) :
    ∃ TQ, (((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (rs.flatMap List.ofFn)) TQ).state = some ⟨.park, true⟩ ∨
        ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (rs.flatMap List.ofFn)) TQ).state = some ⟨.park, false⟩) ∧
      (∀ u < TQ, ∀ b, ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (rs.flatMap List.ofFn)) u).state ≠ some ⟨.park, b⟩) ∧
      (((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (rs.flatMap List.ofFn)) TQ).state = some ⟨.park, true⟩ ↔ nf_allPass N x rs) ∧
      (nf_allPass N x rs →
        ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (rs.flatMap List.ofFn)) TQ).output = [] ∧
        TQ ≤ 4 * (rs.flatMap List.ofFn).length + 10 +
          N.k * ((2 * (2 * N.k + 4) + 12) * rs.length + 15)) := by
  set s := rs.flatMap List.ofFn with hs
  have hslen : s.length = (2 * N.k + 4) * rs.length := nf_stream_length N.k rs
  set V := nf_V N (nf_leaf N) (nf_leafExit N) with hV
  rw [nf_tag]
  -- the control sweep
  obtain ⟨hs1, hs2⟩ := nf_sweep_run N x s
  have hguard0 : ∀ u < 2 * s.length + 2, ∀ q,
      ((nf_M N (nf_leaf N) nf_Ph.ctl).runFrom
        (streamStartCfg x 0 (ScanPhase.fwd (nf_sweepInit N)) s) u).state = some q →
      nf_red N (nf_leaf N) (nf_leafExit N) nf_Ph.ctl q = none := by
    intro u hu q hq
    cases q with
    | done a => exact absurd hq (hs2 u hu a)
    | fwd a => rfl
    | bwd a => rfl
  obtain ⟨hp0, hD⟩ := phaseHostTM_run (nf_M N (nf_leaf N)) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N (nf_leaf N) (nf_leafExit N)) nf_Ph.ctl _ _ (2 * s.length + 2) hs1
    (ScanPhase.done (s.foldl (nf_sweepStep N) (nf_sweepInit N))) (streamStartCfg_state _ _ _ _)
    _ rfl hguard0
  have hwin0 : ∀ u ≤ 2 * s.length + 2, ∀ b, (V.runFrom ((streamStartCfg x 0
      (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
        (Sigma.mk nf_Ph.ctl)) u).state ≠ some ⟨.park, b⟩ := by
    intro u hu b
    rw [hV]
    unfold nf_V
    rw [hp0 u hu]
    exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
  by_cases hpass : nf_sweepPass N (s.foldl (nf_sweepStep N) (nf_sweepInit N)) = true
  swap
  · -- a failed control sweep rejects at the dispatch
    have hver : (V.runFrom ((streamStartCfg x 0
        (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
          (Sigma.mk nf_Ph.ctl)) (2 * s.length + 2 + 1)).state = some ⟨.park, false⟩ := by
      rw [hV]
      unfold nf_V
      rw [hD, Cfg.mapState_state, streamStartCfg_state]
      simp only [Option.map_some]
      rw [if_neg hpass]
    refine ⟨2 * s.length + 2 + 1, Or.inr hver, fun u hu b => hwin0 u (by omega) b,
      ⟨fun h => ?_, fun h => absurd h.1 hpass⟩, fun h => absurd h.1 hpass⟩
    rw [hver] at h
    exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).2 (by simp)
  -- the input's replay
  set dS := streamStartCfg x (0 : Fin 2)
    (ScanPhase.done (s.foldl (nf_sweepStep N) (nf_sweepInit N)) :
      nf_St N (nf_LeafSt N) nf_Ph.ctl) s with hdS
  have hre := nf_retag (N := N) (SL := nf_LeafSt N) (S := nf_St N (nf_LeafSt N) nf_Ph.ctl) dS
    (nf_Ph.rep none) (nf_leaf N none).q₀ (by rw [hdS, streamStartCfg_state]; rfl)
  set dL : Cfg 2 Bool (nf_LeafSt N) x :=
    { state := some (nf_leaf N none).q₀, inputPos := dS.inputPos, workTapes := dS.workTapes,
      workTapePos := dS.workTapePos, output := dS.output } with hdL
  have hinit_state : (N.tm.initCfg x).state = some N.tm.q₀ := by
    rw [NDTM.initCfg_eq, Cfg.init_state]
  obtain ⟨T₁, hpre₁, hpass₁, hrej₁⟩ := nf_leaf_run_in N rs dL (some N.tm.q₀, none, false)
    (N.tm.initCfg x) hne hflag rfl hinit_state.symm
    (by
      show dS.inputPos = _
      rw [hdS, streamStartCfg_inputPos, NDTM.initCfg_eq, Cfg.init_inputPos])
    (by
      intro p hp
      show dS.workTapes 0 (dS.workTapePos 0 + p) = _
      rw [hdS, streamStartCfg_workTapes, streamStartCfg_workTapePos, if_pos rfl, zero_add,
        FinTM.bufferTape_nat])
  have hguard₁ : ∀ u < T₁, ∀ q, ((nf_M N (nf_leaf N) (nf_Ph.rep none)).runFrom dL u).state =
      some q → nf_red N (nf_leaf N) (nf_leafExit N) (nf_Ph.rep none) q = none := by
    intro u hu q hq
    have h := hpre₁ u hu q hq
    show (match nf_leafExit N q with
      | some true => _ | some false => _ | none => none) = none
    rw [h]
  have hrun0 : V.runFrom ((streamStartCfg x 0
      (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
        (Sigma.mk nf_Ph.ctl)) (2 * s.length + 2 + 1) =
      dL.mapState (Sigma.mk (nf_Ph.rep none)) := by
    rw [hV]
    unfold nf_V
    rw [hD]
    simp only [hpass, if_true]
    exact hre
  have hwin1 : ∀ u ≤ T₁, ∀ b, (V.runFrom (dL.mapState (Sigma.mk (nf_Ph.rep none))) u).state ≠
      some ⟨.park, b⟩ := by
    intro u hu b
    rw [hV]
    unfold nf_V
    rw [phaseHostTM_run_le (nf_M N (nf_leaf N)) _ (nf_red N (nf_leaf N) (nf_leafExit N))
      (nf_Ph.rep none) dL T₁ hguard₁ u hu]
    exact nf_tagged_ne_park (fun h => nf_Ph.noConfusion h) _ b
  have hwin01 : ∀ u ≤ 2 * s.length + 2 + 1 + T₁, ∀ b, (V.runFrom ((streamStartCfg x 0
      (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
        (Sigma.mk nf_Ph.ctl)) u).state ≠ some ⟨.park, b⟩ := by
    intro u hu b
    by_cases hu0 : u ≤ 2 * s.length + 2
    · exact hwin0 u hu0 b
    obtain ⟨v, rfl⟩ : ∃ v, u = (2 * s.length + 2 + 1) + v := ⟨u - (2 * s.length + 2 + 1), by omega⟩
    rw [MultiTapeTM.runFrom_add, hrun0]
    exact hwin1 v (by omega) b
  by_cases hin : ∀ r (h : r < rs.length),
      nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] 0
  swap
  · -- a failed input check rejects at the dispatch
    have hrj := hrej₁ hin
    obtain ⟨-, hR⟩ := phaseHostTM_run (nf_M N (nf_leaf N)) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
      (nf_red N (nf_leaf N) (nf_leafExit N)) (nf_Ph.rep none) dL _ T₁ rfl
      nf_LeafSt.rej hrj ⟨.park, false⟩ rfl hguard₁
    have hver : (V.runFrom ((streamStartCfg x 0
        (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
          (Sigma.mk nf_Ph.ctl)) (2 * s.length + 2 + 1 + (T₁ + 1))).state =
            some ⟨.park, false⟩ := by
      rw [MultiTapeTM.runFrom_add, hrun0, hV]
      unfold nf_V
      rw [hR, Cfg.mapState_state, hrj]
      rfl
    have hnp : ¬ nf_allPass N x rs := fun h => hin ((nf_allPass_iff N x rs).mp h).2.1
    refine ⟨2 * s.length + 2 + 1 + (T₁ + 1), Or.inr hver, fun u hu b => hwin01 u (by omega) b,
      ⟨fun h => ?_, fun h => absurd h hnp⟩, fun h => absurd h hnp⟩
    rw [hver] at h
    exact absurd (Sigma.mk.inj_iff.mp (Option.some.inj h)).2 (by simp)
  -- the input passes: the return of tape `0`, then the work tapes
  obtain ⟨hT₁, ip, hcfg⟩ := hpass₁ hin
  set c₁ : Cfg 2 Bool (nf_LeafSt N) x := { dL with
      state := some .pass
      inputPos := ip
      workTapePos := Function.update dL.workTapePos 0
        (dL.workTapePos 0 + ((2 * N.k + 4) * rs.length : ℕ)) } with hc₁
  obtain ⟨-, hR⟩ := phaseHostTM_run (nf_M N (nf_leaf N)) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩
    (nf_red N (nf_leaf N) (nf_leafExit N)) (nf_Ph.rep none) dL c₁ T₁ hcfg
    nf_LeafSt.pass rfl ⟨.aFwd none, .run⟩ rfl hguard₁
  have hre1 := nf_retag (N := N) (SL := nf_LeafSt N)
    (S := nf_St N (nf_LeafSt N) (nf_Ph.rep none)) c₁ (nf_Ph.aFwd none) SeekPhase.run
    (by rw [hc₁]; rfl)
  set c₁' : Cfg 2 Bool SeekPhase x :=
    { state := some .run, inputPos := c₁.inputPos, workTapes := c₁.workTapes,
      workTapePos := c₁.workTapePos, output := c₁.output } with hc₁'
  have hA1 : c₁'.workTapePos 0 = s.length := by
    simp only [hc₁', hc₁, hdL, hdS]
    rw [Function.update_self, streamStartCfg_workTapePos, zero_add, hslen]
  have htape1 : ∀ p, c₁'.workTapes 0 p = FinTM.bufferTape s p := by
    intro p
    simp only [hc₁', hc₁, hdL, hdS]
    rw [streamStartCfg_workTapes, if_pos rfl]
  obtain ⟨c₃, h3, h3s, h3p0, -, h3w, -, h3o, h3win⟩ := nf_aReturn N (nf_leaf N)
    (nf_leafExit N) none s c₁' rfl hA1 htape1
  have h3' : V.runFrom
      ((c₁' : Cfg 2 Bool (nf_St N (nf_LeafSt N) (nf_Ph.aFwd none)) x).mapState
        (Sigma.mk (nf_Ph.aFwd none))) (s.length + 6) =
      c₃.mapState (fun _ => nf_tapeEntry N (nf_leaf N) 0) := h3
  have hc3A : c₃.workTapes 0 = FinTM.bufferTape s := by
    rw [h3w]
    funext p
    exact htape1 p
  have hc3B : c₃.workTapes 1 = fun _ => none := by
    rw [h3w]
    funext p
    simp only [hc₁', hc₁, hdL, hdS]
    rw [streamStartCfg_workTapes, if_neg (by decide)]
  have hc3o : c₃.output = [] := by
    rw [h3o]
    simp only [hc₁', hc₁, hdL, hdS]
    rw [streamStartCfg_output]
  obtain ⟨T₂, hv2, hf2, hacc2, hb2⟩ := nf_V_tail N rs hne hflag N.k 0 (by omega) c₃ h3s
    hc3A h3p0 hc3B hc3o
  have hrun1 : V.runFrom ((streamStartCfg x 0
      (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
        (Sigma.mk nf_Ph.ctl)) (2 * s.length + 2 + 1 + (T₁ + 1)) =
      (c₁' : Cfg 2 Bool (nf_St N (nf_LeafSt N) (nf_Ph.aFwd none)) x).mapState
        (Sigma.mk (nf_Ph.aFwd none)) := by
    rw [MultiTapeTM.runFrom_add, hrun0, hV]
    unfold nf_V
    rw [hR, hre1]
  have hrun2 : V.runFrom ((streamStartCfg x 0
      (ScanPhase.fwd (nf_sweepInit N) : nf_St N (nf_LeafSt N) nf_Ph.ctl) s).mapState
        (Sigma.mk nf_Ph.ctl)) (2 * s.length + 2 + 1 + (T₁ + 1) + (s.length + 6)) =
      c₃.mapState (fun _ => nf_tapeEntry N (nf_leaf N) 0) := by
    rw [MultiTapeTM.runFrom_add, hrun1, h3']
  refine ⟨2 * s.length + 2 + 1 + (T₁ + 1) + (s.length + 6) + T₂, ?_, fun u hu b => ?_, ?_,
    fun h => ?_⟩
  · rw [MultiTapeTM.runFrom_add, hrun2]
    exact hv2
  · by_cases hu1 : u ≤ 2 * s.length + 2 + 1 + T₁
    · exact hwin01 u hu1 b
    obtain ⟨v, rfl⟩ : ∃ v, u = (2 * s.length + 2 + 1 + (T₁ + 1)) + v :=
      ⟨u - (2 * s.length + 2 + 1 + (T₁ + 1)), by omega⟩
    rw [MultiTapeTM.runFrom_add, hrun1]
    by_cases hv1 : v < s.length + 6
    · exact h3win v hv1 b
    obtain ⟨w, rfl⟩ : ∃ w, v = (s.length + 6) + w := ⟨v - (s.length + 6), by omega⟩
    rw [MultiTapeTM.runFrom_add, h3']
    exact hf2 w (by omega) b
  · rw [MultiTapeTM.runFrom_add, hrun2, hacc2, nf_allPass_iff]
    exact ⟨fun h => ⟨hpass, hin, h⟩, fun h => h.2.2⟩
  · obtain ⟨ho, hT₂⟩ := hb2 ((nf_allPass_iff N x rs).mp h).2.2
    refine ⟨by rw [MultiTapeTM.runFrom_add, hrun2]; exact ho, ?_⟩
    rw [hT₁]
    have e2 : (2 * N.k + 4) * rs.length = s.length := hslen.symm
    rw [e2]
    omega

/-- **A stream that first stops the controller is a stream of records**: `n ≥ 1` records of width
`2k + 4`, only the last end-flagged.

**Proof sketch.** The first-stop criterion gives the length `(2k + 4)n` and the flags. Cut the
stream into `n` records of `2k + 4` cells by the product law of `List.ofFn`; the end flag of record
`r` is the stream's cell `(2k + 4)(r + 1) - 1`. -/
private theorem nf_split (k : ℕ) (s : List Bool)
    (hlive : ∀ i < s.length, nf_ctlStop k ((s.take i).foldl (nf_ctlStep k) (0, false)) = false)
    (hstop : nf_ctlStop k (s.foldl (nf_ctlStep k) (0, false)) = true) :
    ∃ rs : List (Fin (2 * k + 4) → Bool), rs ≠ [] ∧ s = rs.flatMap List.ofFn ∧
      ∀ r (h : r < rs.length), rs[r] ⟨2 * k + 3, by omega⟩ = decide (r + 1 = rs.length) := by
  obtain ⟨n, hn, hlen, hfl⟩ := nf_firstStop_records k s hlive hstop
  have hidx : ∀ (r : Fin n) (p : Fin (2 * k + 4)), (2 * k + 4) * r.val + p.val < s.length := by
    intro r p
    rw [hlen]
    have h1 := p.isLt
    have h2 : (2 * k + 4) * (r.val + 1) ≤ (2 * k + 4) * n := Nat.mul_le_mul_left _ r.isLt
    rw [Nat.mul_add, Nat.mul_one] at h2
    omega
  refine ⟨List.ofFn fun r : Fin n => fun p : Fin (2 * k + 4) =>
    s[(2 * k + 4) * r.val + p.val]'(hidx r p), ?_, ?_, ?_⟩
  · exact mt List.ofFn_eq_nil_iff.mp hn.ne'
  · have h := List.ofFn_mul' (m := 2 * k + 4) (n := n)
      (fun i : Fin ((2 * k + 4) * n) => s[i.val]'(by rw [hlen]; exact i.isLt))
    have h0 : List.ofFn (fun i : Fin ((2 * k + 4) * n) => s[i.val]'(by rw [hlen]; exact i.isLt)) =
        s :=
      (List.ofFn_congr hlen (fun i : Fin s.length => s[i.val])).symm.trans (List.ofFn_getElem s)
    rw [List.flatMap_def, List.map_ofFn]
    exact h0.symm.trans h
  · intro r hr
    rw [List.length_ofFn] at hr ⊢
    rw [List.getElem_ofFn]
    have hf := hfl r hr
    have e : (2 * k + 4) * (r + 1) - 1 = (2 * k + 4) * r + (2 * k + 3) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [e, List.getElem?_eq_getElem (hidx ⟨r, hr⟩ ⟨2 * k + 3, by omega⟩)] at hf
    exact Option.some.inj hf

/-- The trivial setup: one state, its own exit. -/
private def nf_P : MultiTapeTM 2 Bool Unit :=
  ⟨(), fun _ _ _ => ⟨0, fun _ => (none, 0), none, some ()⟩⟩

/-- **The backward lemma's obligation `hV`.** For every stream that first stops the controller at
its end, well formed or not in content, the verifier reaches a verdict, `acc` or `rej`, from the
host's entry configuration after the trivial setup, and is at neither before.

**Proof sketch.** The entry configuration is the stream start; the stream is a stream of records;
the characterization gives the first verdict. -/
private theorem nf_hV (N : FinNDTM Bool) (x s : List Bool)
    (hlive : ∀ i < s.length,
      nf_ctlStop N.k ((s.take i).foldl (nf_ctlStep N.k) (0, false)) = false)
    (hstop : nf_ctlStop N.k (s.foldl (nf_ctlStep N.k) (0, false)) = true) :
    ∃ TQ : ℕ,
      (((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (guessRunCfg (nf_P.initCfg x) 0 s
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)) TQ).state =
            some ⟨.park, true⟩ ∨
        ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (guessRunCfg (nf_P.initCfg x) 0 s
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)) TQ).state =
            some ⟨.park, false⟩) ∧
      ∀ u < TQ,
        ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (guessRunCfg (nf_P.initCfg x) 0 s
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)) u).state ≠
            some ⟨.park, true⟩ ∧
        ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (guessRunCfg (nf_P.initCfg x) 0 s
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)) u).state ≠
            some ⟨.park, false⟩ := by
  rw [nf_entry]
  obtain ⟨rs, hne, rfl, hflag⟩ := nf_split N.k s hlive hstop
  obtain ⟨TQ, hv, hf, -, -⟩ := nf_V_char N x rs hne hflag
  exact ⟨TQ, hv, fun u hu => ⟨hf u hu true, hf u hu false⟩⟩

/-- **Checked claims make the decoded virtual run genuine.** If every claim of every record before
the `r`th is checked along the decoded virtual run, then the run after `r` records is `N`'s run
under the records' first `r` choice bits.

**Proof sketch.** Induct on `r`. A record whose claims are all checked decodes to the
configuration's reads at a live state, so the recomputed action is the table's action there under
the record's choice bit, and the virtual step is `N`'s step. -/
private theorem nf_vrun_of_ok (N : FinNDTM Bool) (x : List Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) :
    ∀ (r : ℕ) (_ : r ≤ rs.length), (∀ r' (h : r' < r) (i : Fin (N.k + 1)),
        nf_ok N ((rs.take r').foldl (nf_vstep N) (N.tm.initCfg x)) (rs[r']'(by omega)) i) →
      (rs.take r).foldl (nf_vstep N) (N.tm.initCfg x) =
        N.tm.runWith ((rs.map (fun r => r 0)).take r) (N.tm.initCfg x)
  | 0, _, _ => by rw [List.take_zero, List.foldl_nil, List.take_zero, NDTM.runWith_nil]
  | r + 1, hr, hok => by
    have hlt : r < rs.length := by omega
    have ih := nf_vrun_of_ok N x rs r (by omega) (fun r' h' i => hok r' (by omega) i)
    have hok' : ∀ i, nf_ok N (N.tm.runWith ((rs.map (fun r => r 0)).take r) (N.tm.initCfg x))
        rs[r] i := by
      intro i
      have := hok r (by omega) i
      rwa [ih] at this
    rw [List.take_succ_eq_append_getElem hlt, List.foldl_concat, ih,
      List.take_succ_eq_append_getElem (by rw [List.length_map]; exact hlt),
      NDTM.runWith_append, NDTM.runWith_cons, NDTM.runWith_nil]
    obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp (hok' 0).1
    have hd0 : nf_decode N.k (fun p => some (rs[r] p)) 0 =
        (N.tm.runWith ((rs.map (fun r => r 0)).take r) (N.tm.initCfg x)).inputSymbol :=
      (hok' 0).2
    have hds : (fun j : Fin N.k => nf_decode N.k (fun p => some (rs[r] p)) j.succ) =
        (N.tm.runWith ((rs.map (fun r => r 0)).take r) (N.tm.initCfg x)).workTapeSymbols := by
      funext j
      exact (hok' j.succ).2
    simp only [nf_vstep, hq]
    rw [NDTM.stepWith_of_some hq]
    unfold nf_act
    rw [Option.getD_some, hd0, hds, List.getElem_map]

/-- **The verifier accepts a genuine display.** The display of a branch that is live before its
end, halts at its end and outputs exactly `[true]` passes every check; so the verifier's first
verdict on it is `acc`, with an empty output, within the characterization's bound.

**Proof sketch.** The display is a stream of genuine records, only the last end-flagged. The
control sweep passes it. By strong induction on records, the claims checked so far make the decoded
virtual run the genuine run, live before the end, whose reads the next record's claims are. -/
private theorem nf_V_display (N : FinNDTM Bool) (x w : List Bool) (hw : w ≠ [])
    (hlive : ∀ r < w.length, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state ≠ none)
    (hhalt : (N.tm.runWith w (N.tm.initCfg x)).state = none)
    (hout : (N.tm.runWith w (N.tm.initCfg x)).output = [true]) :
    ∃ TQ, ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (nf_display N x w)) TQ).state = some ⟨.park, true⟩ ∧
      (∀ u < TQ, ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (nf_display N x w)) u).state ≠ some ⟨.park, true⟩ ∧
        ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (nf_display N x w)) u).state ≠ some ⟨.park, false⟩) ∧
      ((nf_V N (nf_leaf N) (nf_leafExit N)).runFrom (streamStartCfg x 0
          (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i)
          (nf_display N x w)) TQ).output = [] ∧
      TQ ≤ 4 * (nf_display N x w).length + 10 +
        N.k * ((2 * (2 * N.k + 4) + 12) * w.length + 15) := by
  obtain ⟨rs, hrs⟩ : ∃ rs, rs = List.ofFn fun r : Fin w.length =>
      let c := N.tm.runWith (w.take r.val) (N.tm.initCfg x)
      nf_record N.k w[r.val] (Fin.cases c.inputSymbol c.workTapeSymbols)
        (decide (r.val + 1 = w.length)) := ⟨_, rfl⟩
  have hdisp : nf_display N x w = rs.flatMap List.ofFn := by
    rw [hrs]
    exact nf_display_records N x w
  have hrlen : rs.length = w.length := by rw [hrs, List.length_ofFn]
  have hget : ∀ r (h : r < rs.length), rs[r] =
      nf_record N.k (w[r]'(by rw [hrlen] at h; exact h))
        (Fin.cases (N.tm.runWith (w.take r) (N.tm.initCfg x)).inputSymbol
          (N.tm.runWith (w.take r) (N.tm.initCfg x)).workTapeSymbols)
        (decide (r + 1 = w.length)) := by
    subst hrs
    intro r h
    rw [List.getElem_ofFn]
  have hne : rs ≠ [] := List.ne_nil_of_length_pos (hrlen ▸ List.length_pos_iff.mpr hw)
  have hflag : ∀ r (h : r < rs.length),
      rs[r] ⟨2 * N.k + 3, by omega⟩ = decide (r + 1 = rs.length) := by
    intro r hr
    rw [hget r hr]
    exact (nf_record_last N.k _ _ _).trans (congrArg (fun n => decide (r + 1 = n)) hrlen.symm)
  have hmap : rs.map (fun r => r 0) = w := by
    apply List.ext_getElem (by rw [List.length_map, hrlen])
    intro r h1 h2
    rw [List.getElem_map, hget r (by rw [List.length_map] at h1; exact h1)]
    exact nf_record_choice N.k _ _ _
  have hok : ∀ r (hr : r < rs.length) (i : Fin (N.k + 1)),
      nf_ok N ((rs.take r).foldl (nf_vstep N) (N.tm.initCfg x)) rs[r] i := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro hr i
      rw [nf_vrun_of_ok N x rs r hr.le (fun r' h' i' => ih r' h' (by omega) i'), hmap]
      refine ⟨hlive r (by rw [← hrlen]; exact hr), ?_⟩
      rw [hget r hr]
      exact nf_decode_record N.k _ _ _ i
  have hall : nf_allPass N x rs := by
    refine ⟨?_, fun i r hr => hok r hr i⟩
    rw [← hdisp]
    exact nf_sweep_display_pass N x w hlive hhalt hout
  rw [hdisp]
  obtain ⟨TQ, -, hf, hacc, hb⟩ := nf_V_char N x rs hne hflag
  obtain ⟨ho, hT⟩ := hb hall
  refine ⟨TQ, hacc.mpr hall, fun u hu => ⟨hf u hu true, hf u hu false⟩, ho, ?_⟩
  rw [hrlen] at hT
  exact hT

/-! ### The transfers -/

/-- The normal form's constant for `k` work tapes, with the record width `W = 2k + 4`:
`6W + k(2W + 12) + 21 + 15k`. -/
private def nf_C (k : ℕ) : ℕ :=
  6 * (2 * k + 4) + k * (2 * (2 * k + 4) + 12) + 21 + 15 * k

/-- The normal form's machine: the controller-stopped host over the trivial setup, the display
controller, and the verifier, guessing on tape `0`. -/
private def nf_host (N : FinNDTM Bool) :=
  guessCtlRunTM nf_P nf_P.q₀ 0 ((0 : Fin (2 * N.k + 4)), false) (nf_ctlStep N.k) (nf_ctlStop N.k)
    false (nf_V N (nf_leaf N) (nf_leafExit N))
    (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i) ⟨.park, true⟩
    ⟨.park, false⟩

/-- **The ledger.** With `|s| = (2k + 4)t₀` and the verifier's time at most
`4|s| + 10 + k((2(2k + 4) + 12)t₀ + 15)`, the host's budget `0 + 2|s| + TQ + 11` is at most
`nf_C k · (t + 1)` for every `t ≥ t₀`.

**Proof sketch.** Collect the budget as `(6(2k + 4) + k(2(2k + 4) + 12))t₀ + 21 + 15k`, raise `t₀`
to `t`, and bound the constant term by `(21 + 15k)(t + 1)`. -/
private theorem nf_ledger (k t₀ t s TQ : ℕ) (ht : t₀ ≤ t) (hs : s = (2 * k + 4) * t₀)
    (hT : TQ ≤ 4 * s + 10 + k * ((2 * (2 * k + 4) + 12) * t₀ + 15)) :
    0 + 2 * s + TQ + 11 ≤ nf_C k * (t + 1) := by
  set A := 6 * (2 * k + 4) + k * (2 * (2 * k + 4) + 12) with hA
  have e1 : 2 * s + (4 * s + 10 + k * ((2 * (2 * k + 4) + 12) * t₀ + 15)) + 11 =
      A * t₀ + (21 + 15 * k) := by
    rw [hs, hA]
    ring
  have h2 : A * t₀ ≤ A * t := Nat.mul_le_mul_left A ht
  have h3 : 21 + 15 * k ≤ (21 + 15 * k) * (t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos t)
  have e4 : nf_C k * (t + 1) = A * t + A + (21 + 15 * k) * (t + 1) := by
    unfold nf_C
    rw [hA]
    ring
  omega

/-- **The forward transfer.** If `N` accepts `x` within `t` steps, the normal form's machine accepts
`x` within exactly `nf_C N.k · (t + 1)` choices.

**Proof sketch.** Cut the accepting word at its first halting time `t₀ ≥ 1`, at most `t`; the
branch is live before `t₀`, halted at `t₀` and outputs `[true]` there, as at `t`. Its display first
stops the controller at its end, and the verifier accepts it at its first verdict, with an empty
output, within the characterization's bound. The host's forward acceptance lemma, after the
trivial setup, accepts at every budget past the ledger's. -/
private theorem nf_forward (N : FinNDTM Bool) (x : List Bool) (t : ℕ)
    (hN : N.AcceptsWithin x t) :
    ∃ w : List Bool, w.length = nf_C N.k * (t + 1) ∧
      ((nf_host N).runWith w ((nf_host N).initCfg x)).state = none ∧
      ((nf_host N).runWith w ((nf_host N).initCfg x)).output = [true] := by
  obtain ⟨w, hw, hh, ho⟩ := FinNDTM.acceptsWithin_iff.mp hN
  -- the first halting time
  have hex : ∃ r, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state = none :=
    ⟨t, by rw [← hw, List.take_length]; exact hh⟩
  classical
  set t₀ := Nat.find hex with ht₀
  have hspec : (N.tm.runWith (w.take t₀) (N.tm.initCfg x)).state = none := Nat.find_spec hex
  have hmin : ∀ r < t₀, (N.tm.runWith (w.take r) (N.tm.initCfg x)).state ≠ none :=
    fun r hr => Nat.find_min hex hr
  have hle : t₀ ≤ t := Nat.find_min' hex (by rw [← hw, List.take_length]; exact hh)
  have hpos : 0 < t₀ := by
    by_contra h0
    have h00 : t₀ = 0 := by omega
    have := hspec
    rw [h00, List.take_zero, NDTM.runWith_nil, NDTM.initCfg_eq, Cfg.init_state] at this
    exact Option.noConfusion this
  set w₀ := w.take t₀ with hw₀
  have hw₀len : w₀.length = t₀ := List.length_take_of_le (by omega)
  have hw₀ne : w₀ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hlive : ∀ r < w₀.length, (N.tm.runWith (w₀.take r) (N.tm.initCfg x)).state ≠ none := by
    intro r hr
    rw [hw₀len] at hr
    rw [hw₀, List.take_take, Nat.min_eq_left hr.le]
    exact hmin r hr
  have hout : (N.tm.runWith w₀ (N.tm.initCfg x)).output = [true] := by
    have hsplit := NDTM.runWith_append (tm := N.tm) w₀ (w.drop t₀) (N.tm.initCfg x)
    rw [hw₀, List.take_append_drop, NDTM.runWith_of_halt _ hspec] at hsplit
    rw [hw₀, ← hsplit]
    exact ho
  -- the verifier on the branch's display
  obtain ⟨TQ, hacc, hfirst, hnil, hTQ⟩ := nf_V_display N x w₀ hw₀ne hlive hspec hout
  obtain ⟨hslive, hsstop⟩ := nf_display_firstStop N x w₀ hw₀ne
  obtain ⟨h0, hst, hfi, hbl, hlf⟩ := nf_setup nf_P x 0
  have hB : 0 + 2 * (nf_display N x w₀).length + TQ + 11 ≤ nf_C N.k * (t + 1) := by
    refine nf_ledger N.k t₀ t _ TQ hle (by rw [nf_display_length, hw₀len]) ?_
    rw [hw₀len] at hTQ
    exact hTQ
  rw [← nf_entry nf_P x (nf_display N x w₀)] at hacc hfirst hnil
  exact guessCtlRunTM_accepts_of nf_P nf_P.q₀ 0 ((0 : Fin (2 * N.k + 4)), false)
    (nf_ctlStep N.k) (nf_ctlStop N.k) (nf_V N (nf_leaf N) (nf_leafExit N))
    ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ ⟨.park, true⟩ ⟨.park, false⟩ 0 (nf_P.initCfg x)
    h0 hst hfi hbl hlf (nf_display N x w₀) hslive hsstop TQ hacc hfirst hnil _ hB

/-- **A passing stream of records is a genuine accepting run.** If every check passes on `n`
records, then `N` accepts `x` within `n` steps, with the records' choice bits as the word.

**Proof sketch.** Passed checks make the decoded virtual run `N`'s run under the choice bits.
The control fold follows the virtual run's state and output summary; the control sweep's pass then
says the run has halted with output summary `[true]`, so with output exactly `[true]`. Claims are
read through `nf_decode` throughout: a record whose presence bit is false reads as blank whatever
its value bit, so the code `01` is no loophole. -/
private theorem nf_backward (N : FinNDTM Bool) (x : List Bool)
    (rs : List (Fin (2 * N.k + 4) → Bool)) (h : nf_allPass N x rs) :
    N.AcceptsWithin x rs.length := by
  obtain ⟨hctl, hok⟩ := h
  set w := rs.map (fun r => r 0) with hw
  have hwlen : w.length = rs.length := List.length_map _
  have hgen : ∀ r ≤ rs.length, (rs.take r).foldl (nf_vstep N) (N.tm.initCfg x) =
      N.tm.runWith (w.take r) (N.tm.initCfg x) :=
    fun r hr => nf_vrun_of_ok N x rs r hr (fun r' h' i => hok i r' (by omega))
  have hfin := hgen rs.length le_rfl
  rw [List.take_length, ← hwlen, List.take_length] at hfin
  -- the control fold follows the virtual run
  have hinit_state : (N.tm.initCfg x).state = some N.tm.q₀ := by
    rw [NDTM.initCfg_eq, Cfg.init_state]
  have hinit_out : StepBlock.outputSummary (N.tm.initCfg x).output = none := by
    rw [NDTM.initCfg_eq, Cfg.init_output, StepBlock.outputSummary_nil]
  obtain ⟨hc1, hc2⟩ := nf_vrun_ctl N rs (N.tm.initCfg x) (some N.tm.q₀, none, false)
    hinit_state.symm hinit_out.symm
  rw [hfin] at hc1 hc2
  have hsw : (rs.flatMap List.ofFn).foldl (nf_sweepStep N) (nf_sweepInit N) =
      ((0, fun _ => none),
        rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d) (some N.tm.q₀, none, false)) :=
    nf_sweep_records N rs _
  rw [hsw] at hctl
  have hout := nf_sweepPass_output N _ _ hc2 hctl
  have hhalt : (rs.foldl (fun d r => nf_complete N (fun p => some (r p)) d)
      (some N.tm.q₀, none, false)).1 = none := by
    unfold nf_sweepPass at hctl
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at hctl
    exact Option.isNone_iff_eq_none.mp hctl.1.1.2
  rw [hc1] at hhalt
  exact FinNDTM.acceptsWithin_iff.mpr ⟨w, hwlen, hhalt, hout⟩

/-- **The backward transfer.** If some choice word halts the normal form's host with output
exactly `[true]`, then `N` accepts `x` at some length.

**Proof sketch.** The host's backward acceptance lemma, with `hV`, gives a stream that first stops
the controller and on which the verifier's first verdict is `acc`. The stream is a stream of
records, and the characterization's first verdict is the same time, since the verifier is at no
verdict before either; so every check passes, and the passing stream is a genuine accepting run. -/
private theorem nf_backward_host (N : FinNDTM Bool) (x w : List Bool)
    (hh : ((nf_host N).runWith w ((nf_host N).initCfg x)).state = none)
    (ho : ((nf_host N).runWith w ((nf_host N).initCfg x)).output = [true]) :
    ∃ t', N.AcceptsWithin x t' := by
  obtain ⟨h0, hst, hfi, hbl, hlf⟩ := nf_setup nf_P x 0
  obtain ⟨s, hslive, hsstop, TQ, hacc, hfirst, -⟩ := guessCtlRunTM_stream_of_accepts nf_P nf_P.q₀ 0
    ((0 : Fin (2 * N.k + 4)), false) (nf_ctlStep N.k) (nf_ctlStop N.k)
    (nf_V N (nf_leaf N) (nf_leafExit N)) ⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ ⟨.park, true⟩
    ⟨.park, false⟩ 0 (nf_P.initCfg x) h0 hst hfi hbl hlf (fun s hl hs => nf_hV N x s hl hs) w hh
    ho
  rw [nf_entry] at hacc hfirst
  obtain ⟨rs, hne, rfl, hflag⟩ := nf_split N.k s hslive hsstop
  obtain ⟨TQ', hv', hf', hacc', -⟩ := nf_V_char N x rs hne hflag
  have hTQ : TQ = TQ' := by
    let V := nf_V N (nf_leaf N) (nf_leafExit N)
    let st : Cfg 2 Bool (Σ i, nf_St N (nf_LeafSt N) i) x := streamStartCfg x 0
      (⟨.ctl, ScanPhase.fwd (nf_sweepInit N)⟩ : Σ i, nf_St N (nf_LeafSt N) i) (rs.flatMap List.ofFn)
    let F : Set (Option (Σ i, nf_St N (nf_LeafSt N) i)) :=
      {some ⟨.park, true⟩, some ⟨.park, false⟩}
    have h1 : Segment V F (fun _ => True) st (V.runFrom st TQ) TQ :=
      (segment_iff _ _ _ _ _ _).mpr ⟨rfl, fun u hu hm => by
        rcases hm with hm | hm
        · exact (hfirst u hu).1 hm
        · exact (hfirst u hu).2 hm, fun _ _ => trivial⟩
    have h2 : Segment V F (fun _ => True) st (V.runFrom st TQ') TQ' :=
      (segment_iff _ _ _ _ _ _).mpr ⟨rfl, fun u hu hm => by
        rcases hm with hm | hm
        · exact hf' u hu true hm
        · exact hf' u hu false hm, fun _ _ => trivial⟩
    exact Segment.time_eq h1 (Or.inl hacc) h2 hv'
  subst hTQ
  exact ⟨rs.length, nf_backward N x rs (hacc'.mp hacc)⟩

end

/-- **The linear-overhead coded normal form** ([BGW70]-style guess-then-verify,
cited through [AB09, §3.2]): every
nondeterministic machine has a coded (two-work-tape) equivalent whose
acceptance tracks the original's at linear time overhead — forward with the
explicit constant, backward in unbounded form (the consumer recovers the
budgeted form from the original's all-branch halting by the truncation
argument, `Turing.NDTM.runWith_of_halt`).

**Proof sketch.** Guess, then verify; this is why codes carry two work tapes.
1. On work tape `0` the simulator guesses a display: one record of `2k + 4` bits per step of
   `N`, holding the step's choice bit, the claimed reads of the input and of each of the `k` work
   tapes (two bits each: `00` blank, `10` false, `11` true) and an end flag, set on the last
   record only. The guess stops at the first record boundary after a set end flag. States and
   actions are not guessed: the verifier recomputes them from `N`'s table in its finite control.
2. A deterministic, silent verifier then reads the display. A control sweep checks the
   recomputed states, the end flags and the output. Replay sweeps check the claimed reads: one
   against the input, and one per work tape `j` of `N` against tape `j` replayed on work tape `1`,
   kept there as one two-cell block per visited cell and rewritten at every record. Between
   sweeps the heads return and the blocks are erased.
3. Each phase is linear in the display, so the simulator runs within `C · (t + 1)` steps, with
   `C = 6W + k(2W + 12) + 21 + 15k` and `W = 2k + 4`: the time is at most
   `(6W + k(2W + 12)) t + 21 + 15k`, and `t + 1` absorbs the additive terms. At `k = 0` the base
   terms still pay for the guess and the control and input sweeps.
4. Forward transfer: a genuine accepting run of length `t` yields an accepting display, guessed
   and verified within `C · (t + 1)`. Backward transfer: a verified display **is** a genuine run
   (the sweeps force consistency), so an accepting branch of the simulator exhibits an accepting
   branch of `N` at some length — unbounded on purpose: runaway guessing branches never accept,
   and no all-branch-halting claim is made for the simulator.
5. The finite state space is relabeled to `Fin`.

**Implementation.** The guess runs under the controller-stopped host `Turing.guessCtlRunTM` with
a trivial setup. The control sweep is a fold by `Turing.scanTM`. A work-tape replay does not
perform the last record's head move, so the blocks stay contiguous around the head. Between sweeps
`Turing.skipTM` and `Turing.skipBackTM` return the heads and `Turing.clearTM` erases the blocks.
The relabeling is `Turing.NDTM.relabelState` (the nondeterministic mirror of
`Turing.MultiTapeTM.relabelState`, as in the `exists_codeTM` precedent). -/
theorem exists_codeNDTM_accepts_linear (N : FinNDTM Bool) :
    ∃ (M : CodeNDTM) (C : ℕ),
      (∀ (x : List Bool) (t : ℕ),
        N.AcceptsWithin x t → M.toFinNDTM.AcceptsWithin x (C * (t + 1))) ∧
      (∀ (x : List Bool) (t : ℕ),
        M.toFinNDTM.AcceptsWithin x t → ∃ t', N.AcceptsWithin x t') := by
  obtain ⟨M, hM⟩ := nf_pack (nf_host N)
  refine ⟨M, nf_C N.k, fun x t hN => (hM x _).2 (nf_forward N x t hN), fun x t hMt => ?_⟩
  obtain ⟨w, -, hh, ho⟩ := (hM x t).1 hMt
  exact nf_backward_host N x w hh ho

end FinNDTM

end Turing
```

## ===== TCSlib/Complexity/ClassP/DTIME.lean =====

```
/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.TuringMachine.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Deciding languages and the classes DTIME

Languages are sets of binary strings, `Mathlib`'s `Language Bool`. A bundled finite
machine over the binary alphabet (`Turing.FinTM Bool`, tape alphabet
`Option Bool = {0, 1, blank}`) *decides* a language `L` in time `T` if on every input `x`
it halts within `T |x|` steps with the single-symbol output `[true]` if `x ∈ L` and
`[false]` otherwise. `DTIME T` is the class of languages decided in time `c · T` for some
constant `c`. [AB09, §1.6, Definition 1.12]

## Design and deviations from [AB09]

* [AB09] fixes the four-symbol alphabet `{▷, □, 0, 1}` for the definition and remarks the
  choice is immaterial. Our machines use the three-symbol tape alphabet
  `Option Bool = {0, 1, blank}` over bidirectional tapes, which need no start symbol
  ([AB09, Claim 1.8] direction). The alphabet-reduction theorem ([AB09, Claim 1.5],
  phase 2) will show that machines over any finite alphabet are simulated by binary ones
  with a constant-factor slowdown — absorbed by the `∃ c` in `DTIME` — so defining
  `DTIME` over binary machines loses no generality.
* Acceptance is by output (`[true]`/`[false]`), not by accepting states: the vendored
  model has a single halting state and distinguishes outcomes by output, which [AB09]
  does via the output tape as well.
* **The output tape is append-only** (the transition emits at most one symbol per step,
  and emitted symbols cannot be erased), whereas [AB09, §1.2] designates a read-write
  work tape as the output tape — [AB09, p. 19] itself lists write-only output among the
  benign model variations. This bridge is **waived** (phase-2 audit, finding 3; see
  the plan's decision log): [AB09]'s read-write-output machine is not formalized in
  this development, so no simulation between the conventions is even statable; the
  compensating restriction is that no exact [AB09] step count is ever imported as a
  formal bound. The in-model buffer-and-flush technique lives in
  `TCSlib.Complexity.TuringMachine.Composition`.
* **Initialization differs from [AB09]**: there are no start-marker (`▷`) cells — the
  bidirectional tapes make them unnecessary — and the input head begins on the first
  input symbol (on the boundary blank for empty input), with all work tapes blank.
* The constant `c` ranges over all of `ℕ`; `c = 0` yields the bound `0`, within which no
  machine can halt (the initial state is not the halting state), so it contributes
  nothing — this matches [AB09]'s `c > 0` without carrying a positivity side condition.

## Main definitions

* `Turing.FinTM.DecidesInTime` — `M` decides `L` within time `T`. [AB09, §1.6 with
  Definition 1.3]
* `Complexity.DTIME` — the class of languages decidable in time `c · T`.
  [AB09, Definition 1.12]

## Main results

* `Complexity.DTIME.mono` — `DTIME` is monotone in the time bound.
* `Complexity.DTIME_eq_empty_of_exists_zero` — a time bound that vanishes at some
  length has an empty class (every machine needs at least one step to halt).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.6; Definitions 1.3, 1.12.)
-/

namespace Turing.FinTM

/-- The machine `M` decides the language `L` within time `T`: on every input `x` it halts
within `T |x|` steps with output `[true]` if `x ∈ L` and `[false]` otherwise.
[AB09, §1.6 with Definition 1.3] -/
def DecidesInTime (M : FinTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime x [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- The class of languages decidable in time `c · T` for some constant `c`: a language
`L` is in `DTIME T` iff some finite binary-alphabet multi-tape machine decides it within
`c · T n` steps on inputs of length `n`. [AB09, Definition 1.12] -/
def DTIME (T : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInTime L fun n => c * T n}

/-- `DTIME` is monotone in the time bound.

**Proof sketch.** A machine deciding `L` within `c · T₁ n` steps also halts (with the
same output) within `c · T₂ n ≥ c · T₁ n` steps, by `Turing.FinTM.ComputesInTime.mono`
(halting is absorbing). -/
theorem DTIME.mono {T₁ T₂ : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) : DTIME T₁ ⊆ DTIME T₂ := by
  rintro L ⟨c, M, hM⟩
  exact ⟨c, M, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- If the time bound vanishes at even one input length, the class is empty: the
initial state is not the halting state, so no machine halts in `c · 0 = 0` steps on an
input of that length (e.g. `List.replicate n false`).

**Proof sketch.** Given `T n = 0` and a claimed decider, instantiate `DecidesInTime` at
the input `List.replicate n false`; the budget is `c * T n = 0`, contradicting
`Turing.FinTM.not_computesInTime_zero`. -/
theorem DTIME_eq_empty_of_exists_zero {T : ℕ → ℕ} (h : ∃ n, T n = 0) : DTIME T = ∅ := by
  obtain ⟨n, hn⟩ := h
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, M, hM⟩
  have hx := hM (List.replicate n false)
  simp only [List.length_replicate] at hx
  rw [hn, Nat.mul_zero] at hx
  exact M.not_computesInTime_zero _ _ hx

end Complexity
```
