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
