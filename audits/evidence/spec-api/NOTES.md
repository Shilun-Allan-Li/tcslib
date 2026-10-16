# The specification API (PR #112): notes

## Why

Two fill deliveries stopped on the same escalation (E1):
- B6 F3 (`fill-b6-configclock.zip`; `audits/evidence/b6-fill-configclock/delivery-review.md`);
- §13d G4 (`fill-s13d-g4.zip`; `audits/evidence/s13d-g4-fill/delivery-review.md`).

Their briefs' ground rule 10 forbade unfolding definitions in the library files the fills cite.
But some facts the routes need are readable only from a definition's body:
- the field layout's base and boundary cells (`fieldsTape`, `fieldOffset`, `joinFields`);
- every row contract's precondition, time, endpoint and envelope (`*_contract`, built through
  `framedContract`);
- the `Contract` combinators' fields (`trans`, `seq`, `inPhase`, `branch`);
- the cells of a record (`RecordAt`), the record length's formula (`recordLength`), and the
  position-width bound (`n + 2 ≤ 2 ^ posWidth n`, previously private as `record_pos_lt`).

The user ruled on 2026-10-16, after weighing a carve-out against an API PR: an API PR first. Proofs
depend on published equation lemmas, not on definition bodies, and this is the rule for future
briefs. Under the §13d rule the PR has its own audit gate.

## What

The patch is `spec-api.patch`, one commit, six files.
- **Generated field equations.** Mathlib's `simps`, with `(config := { isSimp := false })` and the
  explicit projections `pre time post lo hi` (all five `Cfg` fields for the two endpoint
  shapes):
  - `Contract.trans` (`Contract/Basic`);
  - `Contract.seq`, `inPhase`, `branch` (`Contract/Seam`);
  - `framedContract`, `seekPost`, `sweepPost`, and the ten row contracts (`Contract/Catalog`).
    The row contracts' bodies are `framedContract …` applications rather than constructors, so
    they use `simps!`.

  Their statements, as Lean prints them, are in `logs/generated-*.txt` (85 names).
- **Hand-written lemmas:**
  - `Catalog`: `joinFields_nil`, `joinFields_singleton`, `fieldsTape_of_nonneg`,
    `fieldsTape_of_neg`, `fieldsTape_of_length_le`, `fieldsTape_nil`, `fieldOffset_zero`;
  - `CfgRecord`: `recordAt_iff` (`Iff.rfl`); `record_pos_lt` made public (its proof is unchanged);
  - `RecordTable`: `recordLength_eq` (`rfl`).
- Each module docstring's "Main results" lists the additions.

## Design choices

- **No `simp` attribute.** The lemmas are equations only, so no existing `simp` call can change
  behaviour.
- **The attribute lines sit with the definitions' files.** Mathlib refuses a `simps` attribute
  on an imported declaration (checked).
- **`simps!` on the row contracts** reduces their `framedContract` bodies. Some generated
  statements show reduced subterms: `walkTM_contract_pre` reads `w[p]?` where the row states
  `FinTM.bufferTape w p`, the definitional reading at a natural index. The auditor is asked to
  check that each generated statement is the field, with nothing lost.

## Checks (maintainer; against `oleans-lf3p`, #111's replay output, the tip `c2897d7f`)

- **Elaboration** (`logs/elab-*-{base,head}.out`): 0 errors in each file. Warning counts are equal
  to the base: Catalog 77, RecordTable 4, the others 0.
- **Generated names** (`probes/*.checks.lean.txt`, appended to each module):
  - all 85 resolve: 5 in Contract/Basic, 15 in Contract/Seam, 65 in Contract/Catalog;
  - Contract/Catalog's 65 are 5 for `framedContract`, 5 each for `seekPost` and `sweepPost`,
    and 50 for the ten rows.
- **Axioms** (`logs/axioms.log`): the ten hand-written lemmas are within
  `[propext, Classical.choice, Quot.sound]`.
- **Freeze** (`logs/freeze.log`): publics added only. `record_pos_lt` moves from private to
  public with its statement unchanged.
- **Lint** (`logs/lint-{base,head}.txt`): 0 FAIL, 14 WARN over 36 files, as at the base. No added
  line over 100 characters.
- **Screen** (`logs/screen-{base,head}.txt`, `logs/screen-delta.log`): 711 → 712 declarations,
  350 pairs before and after, 0 new pairs.
- **Replay:** `replay-lapi.sh` over `replay-order.txt` (89 modules). #112 is stacked on #113
  (the cont5 partial, whose closure overlaps), so the replay starts from #113's snapshot
  `oleans-lc5p`. The user runs both, chained (user, 2026-10-16).
