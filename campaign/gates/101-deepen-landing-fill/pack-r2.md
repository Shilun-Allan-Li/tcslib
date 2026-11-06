# External audit pack, round 2: the deepening fill's landing, `Complexity.savitch` (PR #208, a fill gate)

**Round 1** (`pack.md`; findings `findings.md`; dispositions `resolutions.md`) was **HOLD, 0
blockers, 1 major, 3 minors, 3 notes**, with no soundness defect. Notes 5–7 verified the contract,
its edge cases, the pins, the freeze and the static evidence. The issues were:
- **Finding 1 (major):** the value-to-width bound `m ≤ 2^e → |bits (m + 1)| ≤ e + 2` was proved
  three times, in `Deepen`'s `deepen_contract`, `ARMWidth`'s `arm_decides_pspace_val` and
  `ISCountGenCorrect`'s private `bits_succ_le`, in no ledger family;
- **Finding 2 (minor):** `Savitch.lean`'s proofs read `NSPACE`, `DeepenContract` and
  `SpaceConstructible` directly, and the pack's exception named only the second;
- **Finding 3 (minor):** two prose bounds were stronger than the invariants (`dp_run`'s sketch,
  `Savitch.lean`'s Design bullet);
- **Finding 4 (minor):** `deepen_contract`'s docstring had no source tag.

**The user ruled on finding 1: harvest in #208, all three** (2026-11-06). Preparing round 2, the
screen (with the newly changed files added) exposed a second, older family, **IL-1**: six proofs
re-derive the public `indicator_inputLenLang`. **The user ruled: re-point all six in #208.**
Its simp-set variants were then found: five more readings re-derive `indicator_inputLenLang` or
its sibling `indicator_inputBitLang`. **The user ruled: re-point all five too**; the ledger's IL-1
is widened by kind to both readings.

**The PR:** #208 on `lean/ch34-deepen-landing`, head
`36ed2deb6023bb1392ee64130c608f9fcf80a3fb`: round 1's head `a074d9b7`, the campaign merge
`ca0af1c0` (#209, no change to the PR's files), the repair `9db4f2ee`, the IL-1 re-points
`6a289c50` and `0140aee2`, and records-only campaign merges (`dd8a52c5`, `d01c56a4`,
`36ed2deb`). It now changes thirteen files: round 1's three (`Deepen`, `Savitch`, the facade);
`Machines/Bin`, `Machines/ARMWidth` and `Logspace/ISCountGenCorrect` (finding 1); and `ExpBFS/Main`, `SavitchARM/Correct`,
`Machines/ARMWidthExample`, `Logspace/PathHardRegs`, `Randomized/SpaceAmplifyPoly`,
`Logspace/PathWalkMachine` and `Logspace/Mult` (IL-1).

## What changed since round 1 (verify)

| Finding | Change (`9db4f2ee`, IL-1 `6a289c50`) |
|---|---|
| 1 | **Harvested.** `Complexity.LogProg.length_bits_succ_le` (`h : m ≤ 2 ^ e + 1 → (Nat.bits (m + 1)).length ≤ e + 2`) in `Machines/Bin`, beside `length_bits_le`, with a sketch and the module's results list. `ISCountGenCorrect`'s private `bits_succ_le`, the same statement, is deleted and its one use re-pointed; the inline `hlt` blocks of `arm_decides_pspace_val` and `deepen_contract` are replaced by `length_bits_succ_le ((h r).trans (Nat.le_succ _))`. The ledger records the family as **BL-2** (`campaign/duplication-ledger.md`), retired on #208's merge, with a library search for other members |
| 2 | `savitch` reads `SpaceConstructible` through `spaceConstructible_iff`. The two remaining reads are recorded exceptions (`resolutions.md`): `NSPACE`'s set-builder body has no published characterization, and the brief forbids `DeepenContract`'s `_iff`. The seal covers `Deepen` only, not `Savitch.lean` |
| 3 | The Design bullet and `PSPACE_eq_NPSPACE`'s sketch bound the search registers by `2 ^ (w · w)`, `O(w²)` digits; `dp_run`'s sketch bounds the setup values by `max |x| (1 + |bits |x||)` and the loop's by `2 ^ (dpW · dpW)` |
| 4 | `deepen_contract`'s docstring says the machine never computes `sp` and searches at radius `1, 2, …`, tagged [Sip13, §8.1, proof of Theorem 8.5] and [AB09, Theorem 4.14]; its sketch cites `length_bits_succ_le` |
| IL-1 | **Re-pointed** (`6a289c50`). Each site unfolds its decider table and cites `Complexity.indicator_inputLenLang` in place of repeating `inputLenLang`, `indicator_indexLang_pairEncode`, `decide_eq_decide.mpr Iff.rfl`: `ISCountGenCorrect`'s `gen_start`, `ExpBFS/Main`'s `orcN_len`, `SavitchARM/Correct`'s `NSPACE_poly_subset_PSPACE`, `ARMWidthExample`'s `searchLang_mem_PSPACE`, `PathHardRegs`' `orc_len` and `SpaceAmplifyPoly`'s `ps_start`; then (`0140aee2`) the simp-set variants, citing `indicator_inputLenLang` or `indicator_inputBitLang`: `PathWalkMachine`'s `pathOr_len` and `pathOr_bit`, `PathHardRegs`' `orc_bit`, and both halves of `Mult`'s private `mult_queries`. A grep of every code line naming either language finds no other unfolding. The ledger's **IL-1** (widened by kind), retired on #208's merge |

No statement changes except the new public lemma (`evidence/round2/freeze/`):
- `Bin` 15 → 16 public (`length_bits_succ_le`);
- `ARMWidth` 5 public, `arm_decides_pspace_val`'s body;
- `ISCountGenCorrect` 7 public, 2 → 1 private (`bits_succ_le` removed), `compl_mem_NSPACE`'s and
  `gen_start`'s bodies;
- IL-1's seven other files: the bodies above (`Mult`'s private `mult_queries`;
  `PathHardRegs` and `PathWalkMachine` two each), no statement change;
- `Savitch` 2 → 3 public as in round 1, `savitch`'s body; `PSPACE_eq_NPSPACE`'s docstring only;
- `Deepen` 2 public and 43 private, as in round 1.

## Brief for the auditor

1. **Finding 1 and IL-1:** is `length_bits_succ_le` the right statement and home, are all
   sites of both families re-pointed, and do BL-2 and IL-1 describe them? Is any member left in
   the library?
2. **Findings 2–4:** are the exceptions precise, and are the new texts accurate and attributed?
3. **The repair itself:** does it re-derive anything, or change anything beyond the findings?

## Repository-side attestations (verify or challenge)

- **Replay** (`evidence/round2/merged-tree/`): `replay-ldp6` at `36ed2deb`, the downstream closure
  of the thirteen files (190 modules, `Machines/Bin`'s), chained from the campaign's `oleans-lnth`:
  **190 modules, 0 failed**; static 0 mismatches (39 `sorry` warnings, all in modules outside the
  PR's files, the campaign's existing ones).
- **Rule 10** (`evidence/round2/seal/`): round 1's generator re-run on the head's `Deepen.lean`
  seals the same 35 definitions (the sealed copy is byte-identical to round 1's regeneration, as
  `Deepen.lean` did not change after `9db4f2ee`). On `oleans-ldp6` it elaborates with **0
  diagnostics**; the controls fail at all 35 sealed goals, at the same positions as round 1's.
- **Axioms** (`evidence/round2/axioms/`, on `oleans-ldp6`): the seventeen headline and re-pointed declarations,
  `savitch`, `savitch_of_logSpace_le`, `deepen_contract`, `NPSPACE_subset_PSPACE`,
  `length_bits_succ_le`, `arm_decides_pspace_val`, `compl_mem_NSPACE`, IL-1's ten
  (`gen_start`, `orcN_len`, `NSPACE_poly_subset_PSPACE`, `searchLang_mem_PSPACE`, `orc_len`,
  `ps_start`, `pathOr_bit`, `pathOr_len`, `orc_bit`, `multLang_mem_LOGSPACE`), all on
  `[propext, Classical.choice, Quot.sound]`.
- **Screen** (`evidence/round2/screen/`): round 1's 20 files plus the seven changed files outside
  it (`Machines/Bin`, `ISCountGenCorrect`, `PathHardRegs`, `ARMWidthExample`,
  `SpaceAmplifyPoly`, `PathWalkMachine`, `Mult`), on `git archive`s of the head and its base (the campaign's Lean,
  `0b05cc3a`):
  the head (27 files) **420 declarations, 128 pairs, 32,575 characters**; the base (26; `Deepen` is
  new) 390, 152, 34,548. **0 new pairs**; the 24 gone are IL-1's (its members against
  `indicator_inputLenLang`, `orcN_len`, `orc_len` and `orc_bit`), and no pair has a `Deepen`
  declaration on either side.
- **Lint** (`evidence/round2/lint/`): the campaign lint on `SpaceComplexity` 0 FAIL, 81 WARN over
  112 files at the head (80 over 111 at the base; the one new WARN is round 1's `DeepenContract`
  check 8), and on `Randomized` 0 FAIL, 51 WARN over 65 files at both. The policy linter over the
  twelve changed modules (the facade has no declarations): the same 8 findings at base and head,
  all pre-existing: `Mult`'s size and five proofs without a sketch, `bits_getLast`
  (`Machines/Bin`) and `runVal_two_ge` (`SpaceAmplifyPoly`).
- Round 1's delivery, review and sweep evidence are unchanged.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/101-deepen-landing-fill/findings-r2.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `deepen-landing-fill-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
