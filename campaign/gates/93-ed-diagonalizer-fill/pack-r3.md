# External audit pack, round 3: E-D's landing (PR #188, a fill gate)

**Round 2** (`pack-r2.md`; findings `findings-r2.md`; resolutions `resolutions.md`) was **DO NOT
CLOSE, 0 blockers, 2 majors, 0 minors**. Round 1's repairs and record corrections were accepted.
The two majors were further inline re-derivations: `dz_split_tape`'s prefix branch
(`FinTM.bufferTape_take`) and `dz_top_run`'s output after the halt
(`MultiTapeTM.runFrom_output_eq_of_halt`).

**Ruled (user, 2026-11-04): fix both, and acknowledge the kind.** Any further inline step in
`NTimeDiagonalizer` that re-derives a published run, buffer or segment lemma is the family
**ED-IN**, scoped by kind, for the dedup window (`campaign/duplication-ledger.md`, "E-D's
delivery"). Under TEMPLATE's failure mode 5, a later find of this kind is an accounting minor.

**The PR now:** #188 at `935245f483e776dced796552d649434bb64ec16b`:
- `49ffc047`, the fix (`evidence/round3/patches/`);
- then a merge of campaign records, which changes no Lean.

## What changed since round 2 (verify)

| Site | Change |
|---|---|
| `dz_split_tape`, the branch `0 ≤ q < |s₁|` | `(s₁ ++ [b] ++ w).take |s₁| = s₁` by `List.take_left'`, then `← FinTM.bufferTape_take (s₁ ++ [b] ++ w) |s₁| h3.2` |
| `dz_top_run`, `hsame` | `MultiTapeTM.runFrom_output_eq_of_halt BF.tm c0 hle hst0` (the output equality the next line uses) |
| `dz_cell0`; `dz_top_run`'s flag cell `e`; `dz_setup_facts`' block cell | cite `FinTM.bufferTape_nat`, the natural-cell read, instead of unfolding `bufferTape_eq`. Found by the maintainer's sweep for the kind (below) |

## Brief for the auditor

1. Are the five replacements correct, statement-preserving and rule-10 compliant? Note that the
   three `bufferTape_nat` citations use `simpa` with the default `simp` set; the seal re-run
   covers them.
2. **The sweep** (`evidence/round3/sweep.txt`): at `49ffc047`, the new declarations (lines ≥ 5347)
   contain no `bufferTape_eq` unfolding, `Nat.exists_eq_add_of_le`, `runFrom_add`,
   `lt_trichotomy` or `Nat.find`. It is a candidate enumeration with inspection, not a proof of
   absence. Under ED-IN, any further find is a minor.
3. Is the ED-IN record right?

## Repository-side attestations (verify or challenge)

- **Elaboration:** the fixed file elaborates against `oleans-led` with no output.
- **Rule 10** (`evidence/round3/seal/`): the review's seal generator re-run on the fixed file. Of
  the 350 definitions, every one has a control that passes unsealed and fails sealed, and none
  passes sealed. The sealed copy elaborates with 0 errors.
- **Axioms** (`evidence/round3/axioms.out`): `dz_split_tape`, `dz_top_run`, `dz_cell0`, `dz_first`,
  `dz_split` and `exists_diagonalizer` on `[propext, Classical.choice, Quot.sound]`.
- **Replay:** `replay-led3` (`evidence/round3/merged-tree/`) covers `NTimeDiagonalizer`,
  `NTimeHierarchy` and `Diagonalization`, chained from `oleans-ledge`. Round 2's replay,
  `replay-led2`, passed (`evidence/round2/merged-tree/`, its log now attached).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/93-ed-diagonalizer-fill/findings-r3.md`. The gate closes when it has zero blockers
and zero majors.

**Deliver your findings as a downloadable Markdown file named `ed-diagonalizer-fill-r3-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
