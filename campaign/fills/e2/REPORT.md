# Fill report — epoch E2 (the counting layer over an abstract verifier model)

Plan §5 orders the P1 fills as epoch E1 (the pure-math `Quantum/Basic` lemmas), then E2 (the
counting layer against an abstract model) and E3 (the polynomial-time closure facts). This report
covers E2. The audited baseline is the closing commit of gate `quantum-phase1`,
`13c8664b44f2550a66a8fb2c94c73069614f072f`.

| Item | Value |
|---|---|
| Branch | `quantum/e2-fill` (from `quantum/p1-basic`, independent of `quantum/e1-fill`) |
| Fill commit | `b3f49f4d` |
| Files owned | `TCSlib/Complexity/Promise/Basic.lean`, `TCSlib/Complexity/Counting/{PP, GapP, Inclusions}.lean` |
| Targets | the 22 sorried statements stated against an abstract `VerifierModel`: `Promise/Basic` (3), `Counting/PP` (2), `Counting/GapP` (15), and the two model-generic results of `Counting/Inclusions` (`InBPP.inPP`, `InPP.compl`) |
| Result | **all 22 proved** |
| Not in E2 | the 11 statements about `Randomized.polyTimeModel` (E3): the 8 closure facts of `Counting/PolyTime.lean` and the 3 corollaries of `Counting/Inclusions.lean` that use them (`inPP_polyTimeModel_compl`, `inPP_polyTimeModel_of_mem_NP`, `inPP_polyTimeModel_headD`), untouched |

**Process deviation.** `workflow.md` §4 runs epochs in sequence, each after the previous epoch's
boundary audit. E2 was started while the E1 boundary audit was still pending, at the owner's
request, to use the waiting time. Isolation is by files: E1 owns `TCSlib/Quantum/Basic/**`, E2
owns the four files above, the two sets share no file, and neither imports the other. E2 builds
on the gate baseline, not on E1. If the E1 audit changes anything, E2 is unaffected; the E2
boundary audit can run on its own or together with a later round. Recorded in the plan's decision
log.

## Verification (MEASURED, `evidence/logs/`, scripts in `evidence/scripts/`)

The scripts are E1's, unchanged except for the file list of `copy_screen.sh` and a comment in
`Axioms.lean`.

- **Sweep (`sweep.log`).** All 14 P1 modules pass `scripts/lean_check_tree.sh` in dependency
  order (direct `lean`, never `lake build`), with no diagnostic other than `sorry` warnings.
  `Promise/Basic`, `Counting/PP` and `Counting/GapP` report none at all. The total is 63 `sorry`
  warnings: 52 in `Quantum/Basic` (E1's targets, filled on `quantum/e1-fill`, not on this
  branch), 8 in `Counting/PolyTime` and 3 in `Counting/Inclusions` (E3).
- **Axioms (`axioms.log`).** 248 constants. Of the 95 in the `Promise` and `Counting` modules,
  84 depend only on `propext`, `Classical.choice` and `Quot.sound` (21 of them on no axiom). The
  11 `sorryAx` dependents are exactly the 11 E3 statements. (The other 90 `sorryAx` rows are
  `Quantum` constants on this branch, before E1's fill is merged.)
- **Statement freeze (`drift.log`, `drift.py`, comparing signatures and full bodies).** From 212
  declarations at the baseline to 223:
  - **0 removed;**
  - **0 signatures changed;**
  - **22 bodies changed**, exactly the 22 filled statements;
  - **11 added**, all private (below);
  - 190 unchanged in signature and body.
- **Style (`style_lint.log`, `campaign_style_lint.log`).** `style_lint.py` reports 0 findings
  over the four E2 files; `campaign_style_lint.py`, run over the whole tree, reports 0 FAIL and
  0 WARN for all 14 audited files and the facades. No line exceeds 100 characters.

## New public declarations: none

No audited declaration was renamed, re-signed or restated, and no public declaration was added.

## Private helpers (11), all in `GapP.lean`

Under a new heading, *The gap as a signed sum, and splitting random strings*, placed before the
first lemma that needs it:

- `sgn` (accept `1`, reject `-1`, abstain `0`) and `sgn_eq` (its two-indicator form);
- `gap_eq_sum`: the gap is `∑_r sgn (M x r)` over the `2^m` strings. Every gap computation goes
  through this one form;
- `sum_append` (`Fin.appendEquiv`) and `sum_cons` (`Fin.consEquiv`): a sum over strings of length
  `a + b` or `m + 1` as a double sum over the parts;
- `all_not_ofFn`: a string is all `false` iff it is the constant `false` string (used by
  `gap_padVerifier` and `gap_constVerifier`);
- `gap_boolVerifier_int_aux`: the proof of the audited `gap_boolVerifier_int`. The audited file
  states `gap_boolVerifier` (over `ℚ`) before `gap_boolVerifier_int` (over `ℤ`), and the first is
  proved from the second, so the proof sits in a helper ahead of both instead of reordering
  audited declarations (the same device as E1's `superdenseState_vec_aux`);
- `gap_coinFill`: `coinFill M p`, read as a Boolean verifier, has `2^(d+1)` times `M`'s gap. Used
  by `randProb_coinFill`;
- `polyLen_le_polyLen`, `polyLen_succ_le`: schedule domination;
- `IsGapP.common_schedule`: two gap functions have verifiers on one common schedule. Used by
  `IsGapP.add` and `IsGapP.mul` (see the ledger).

## Duplication ledger

Screened with `scripts/copy-text-screen-v3.py` over the four E2 files
(`evidence/scripts/copy_screen.sh`, `evidence/logs/copy_screen.log`).

**Removed before this report.** The first screen found `IsGapP.mul` reproducing about 80% of
`IsGapP.add`: both padded the two verifiers to a common schedule with the same eight lines. That
step is now the private `IsGapP.common_schedule`, and both proofs are three lines on top of it.

**Remaining pairs at the fill commit: 8.** None reproduces the proof of the same fact.

| Pairs | What is shared | Classification |
|---|---|---|
| 6 among `InPP`, `InPromisePP` (`PP.lean`) and `InPromiseBPP` (`Promise/Basic.lean`) | the shape `∃ M a k, E.Eff (boolVerifier M) ∧ ∀ x, …` | Definitions, unchanged since the gate (audited there); each is a different class, and the same shape is `Randomized.InBPP`'s |
| `gap_padVerifier` / `gap_constVerifier` (148 characters) | `rw [gap_eq_sum, …]; Finset.sum_eq_single (fun _ => false)` with `all_not_ofFn` | Idiom; both reduce to the one all-`false` string, for different verifiers |
| `gap_coinFill` / `gap_prodVerifier` (175 characters) | `rw [gap_eq_sum, sum_append …]` and a per-summand case split on the answer | Idiom; the shared steps are already the private `gap_eq_sum` and `sum_append` |

- **Copies of proved material: none.** The proofs use Mathlib, the audited statements and
  `Randomized.randProb_bool_false`. The screen covers only the E2 files; no counting-layer lemma
  exists elsewhere in the repository to copy (the gate's duplication ledger, unchanged).

## Notes for the epoch-boundary audit

- **Sketches synchronized (policy §3).** Four sketches written at skeleton time described routes
  the fills did not take and were rewritten to describe the proof that is there:
  `randProb_cast_eq_sum` (`PP.lean`), and `abs_gap_le`, `gap_negVerifier`, `randProb_coinFill`
  (`GapP.lean`), all three now through `gap_eq_sum`, `randProb_coinFill` through the private
  `gap_coinFill`. Docstring changes only; the drift check strips comments. The other 18 sketches
  match their proofs as written at the gate.
- `IsGapP.add`'s sketch still names the explicit common schedule
  `polyLen (a₁ + a₂) (max k₁ k₂)`; the proof obtains it from `IsGapP.common_schedule`, whose
  proof builds exactly that schedule.
- The proofs involve no TCSlib machine construction or host (policy §1, *Hosts come first*): all
  machine-level content is behind the named closure hypotheses, which E3 discharges for
  `polyTimeModel`.
- **Merging.** `quantum/e1-fill` and `quantum/e2-fill` touch disjoint Lean files. Both append a
  row to the plan's decision log, so the second merge has a one-line conflict there, resolved by
  keeping both rows in date order.
