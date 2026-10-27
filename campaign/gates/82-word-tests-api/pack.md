# External audit pack — the linear word tests (PR #171, an API gate)

**Why this PR.** Megafill D's E-Q partial (`campaign/fills/eq/reviews/fill-cp1/REVIEW.md`, F2 and
F11) found that a Boolean fixed-word decider and a linear all-`true` decider are argued privately in
four files. Those are `Nondeterminism`'s `a3n_` lemmas, `TMSAT`'s `tmsat_` twins, `EXPCOM`'s
`expcom_all_true`, and E-Q's `qy_guard_decider`. All of them are built from the same public rows.
**The user ruled (2026-10-27): an API PR first, publishing the rows and re-pointing every copy.**
E-Q's checkpoint 1 landing (a later PR) then cites them.

**The PR:** #171 on `lean/word-tests`, head `d17f63c8110a5647df8535d52284db896f9c96fb`, two commits
on the campaign tip, whose Lean is the tree after #169 (`evidence/patches/`):
- `dc8da676`: the new module `TuringMachine/Build/WordTests.lean`, the `TuringMachine` facade's
  import and entry, and the Build README's row;
- `d17f63c8`: the re-points in `ClassNP/Nondeterminism`, `ClassNP/TMSAT` and
  `Diagonalization/EXPCOM`.

## What changed (verify)

| Class | Declarations |
|---|---|
| **New public** (`Build/WordTests`) | `Turing.incFixed_ne_some_nil`, `Turing.incFixed_getD_eq_nil_iff`, `Turing.FinTM.computesFunInTime_decideEq`, `Turing.FinTM.computesFunInTime_allTrue` |
| **Re-proved as citations** | `a3n_poly_fixed_eq`, `a3n_poly_unary`, `tmsat_pt_eq`, `tmsat_pt_unary` (private; statements unchanged); `expcom_ok_iff`'s one step now cites `incFixed_getD_eq_nil_iff` |
| **Removed** (private) | `a3n_inc_none` and `tmsat_inc_none`, each a copy of the published `incFixed_eq_none_iff_replicate`; `a3n_inc_nonempty`, `tmsat_inc_nonempty`; `expcom_all_true` |
| **Frozen** | every public statement of the three files (8, 6, 9 unchanged) |

## Brief for the auditor

1. **The rows.** Are the four statements the right public forms?
   - The one-bit reading `[decide (x = w)]` is what `computesFunInTime_cond`'s test takes.
   - The constant in `computesFunInTime_decideEq` depends on `w`, after `∃ M c`.
   - The all-`true` test is linear, including on the empty word.
   - The overflow criterion is stated in its `getD` form.

   Are the proofs correct, and is `computesFunInTime_allTrue`'s composition bound sound (the
   increment's output is at most as long as its input)?
2. **The home.** A new leaf module importing only `Build/Primitives`, so that the consumers' import
   of it is their only change. Two choices are disclosed:
   - **Not beside the rows.** Putting the lemmas beside `computesFunInTime_ifEq`
     (`Composition`) or `computesFunInTime_incFixed` (`Primitives`) would replay most of the
     library, as the E-Q review noted.
   - **No `Mathlib.Tactic.Linarith`.** A first version imported it, and that import broke an
     unrelated `simp` step in `TMSAT` (`evidence/consumers/TMSATCat-with-Linarith.out`). The
     `nlinarith` step is now a ring identity. Is the home right?
3. **Rule 10** (with the scope of 2026-10-23). The module is sealed over `incFixed`,
   `FinTM.ComputesFunInTime` and `FinTM.ComputesInTime`; the sealed copy elaborates
   (`evidence/WordTestsSealed.*`).
   - Its 3 controls close unsealed and fail sealed, each at its own goal
     (`evidence/WordTestsSealControl.*`). `incFixed`'s control is the usage form: the
     recursive definition on a concrete word.
   - Is any other-file definition passed to `simp` or `rw`, or closed by reduction?
   - The removed privates unfolded `incFixed` by `simp [incFixed]`; their replacements do not.
4. **The re-points.** Do the three files keep every public statement and their behaviour?
   - Each was elaborated with the module inlined in place of its import
     (`evidence/consumers/*Cat.*`): 0 errors.
   - Their warnings are the base's (`*Base.out`): `Nondeterminism` 37 and 37, `TMSAT` 0 and 0,
     `EXPCOM` 0 and 0.
   - Freeze: `evidence/consumers/freeze-*.txt`.
5. **Duplication.**
   - Is any copy of these tests left? `Savitch`'s inline `hD'`, the `[decide (x = [])]` conversion,
     is not in the ruling's scope; it is a candidate for the dedup window.
   - `Nondeterminism`'s private `a3n_poly_linear` is the public `polyTimeComputable_of_linear`'s
     twin, also left for that window.
   - Does any new row re-derive a published lemma?
6. **Records.** Is the PR's account (the module's docstring, the facade's entry, the README row)
   accurate and public-facing?

## Repository-side attestations (verify or challenge)

- **Elaboration** against `oleans-laplusm` (the campaign's snapshot after #169):
  - the module with its four axiom prints: 0 diagnostics; `incFixed_ne_some_nil` and
    `incFixed_getD_eq_nil_iff` on `[propext]`, the two `FinTM` rows on
    `[propext, Classical.choice, Quot.sound]` (`evidence/WordTestsAx.*`);
  - the sealed copy: the same.
- **Lint** (`evidence/lint-head-*.txt`): `TuringMachine` 0 FAIL, 68 WARN over 85 files (the module
  adds no warning); `ClassNP` 0 FAIL, 16 WARN over 21 files, as at the base but for two shorter
  size lines (`lint-base-ClassNP.txt`); `Diagonalization` 0 FAIL, 2 WARN over 5 files.
- **Replay:** the downstream closure of the changed modules, 18 modules (`evidence/down-lwords.txt`;
  `CookLevin/Hardness`, `CircuitComplexity/PSubsetPPoly`, `ClassOracle/SATOracle` and
  `Randomized/PolyTimeModel` among them). It is chained after #170 if #170 merges first (both
  touch `EXPCOM`). **Pending.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `campaign/standards/TEMPLATE.md`. Findings go verbatim into
`campaign/gates/82-word-tests-api/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `word-tests-api-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
