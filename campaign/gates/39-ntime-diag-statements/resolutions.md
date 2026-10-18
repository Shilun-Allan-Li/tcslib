# C1-E's statements, the lazy diagonalizer (PR #121): resolutions

**Gate:** PR #121, the statement gate for `Diagonalization/NTimeDiagonalizer` (namespace
`Turing.NTimeDiag`): the stages, the stage query, and the contracts `exists_queryTM` (fill E-Q)
and `exists_diagonalizer` (fill E-D).
- Pack: `audits/ntime-diag-statements-pack.md`, preserved as dispatched.
- Round 1 bundle SHA-256: `0eb7578e…3c9a` (folder
  `infra_local/gate-dispatches/39-ntime-diag-statements-gate/`; Lean `13f52659`).

## Round 1

The findings are in `audits/ntime-diag-statements-findings.md`, verbatim. **FAIL: 0 blockers,
1 major, 2 minors, 1 note.** The auditor found the stages, the query and both contracts' statements
true and sufficient; the major is in `exists_diagonalizer`'s proof sketch.

The maintainer's review sub-agent verified every finding at `13f52659`, with elaborations against
`oleans-lndiag` (`$S/review/ntime-diag-gate/REVIEW.md`). All are true, at the auditor's
severities. **No statement changes.**

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The sketch's middle completeness used R's prefix clause in the design's old form, `C_R·(t' + 1) + 2|bits (g n)|`. The gated clause is `C_R·(t' + |x| + |bits (g n)| + 1)`, with `|x| = n + 1`, and a per-code multiple of `n` cannot be absorbed into the uniform `K` when `g n = n`. | **True. The user's ruling (2026-10-17): the guessed budget**, the alternative already named in C1's design §3.6. In the middle, D guesses a nominal budget `b` of `bits (g n)`'s width, rejects unless `b ≤ g n`, normalizes it to `bits b`, and runs R on `⟨⟨bits b, α⟩, 1^{n+1}⟩`. Completeness takes `b = t'` and uses R's **total-time clause**, `T ≤ C_R·(b + 1)`, which has no `|x|` term. Soundness: an accept is acceptance within `b ≤ g n` (`AcceptsWithin.mono`), and a guess below every acceptance time rejects. The review checked each step, including the test `b ≤ g n` as what gives R's hypothesis `t ≤ |s|`. **Fixed in round 2:** `exists_diagonalizer`'s sketch is rewritten (docstring only). The design records are corrected (below). |
| 2 | minor | The sketch's `K` was both the clock's body allowance and the physical-time coefficient. | **True. Fixed in round 2** (the same docstring): the body allowance is `g n`; the clock's physical cost is at most `5·g n + 2|bits (g n)| + 2 ≤ 7·(g n + 1)` (`exists_stepClockTMVia`); setup costs `P·(g n + 1)` and the final dispatch a constant `P'`; `K = P + 7 + P'`. |
| 3 | minor | `stage` for `n ≤ 2` and `query` off its guard have no published equation (policy §1). | **True. Fixed in round 2:** `stage_of_le_two` (`stage f n = 0` for `n ≤ 2`) and `query_of_not_guard` (`query f g x = []` unless `x` is unary of length at least 3), with the Main-results list updated. Both proved, standard axioms. |
| 4 | note | The bundle has no PR body and no `TimeHierarchy/Diagonal.lean`, the screen population's seventh file. | **Records.** The PR body is at `audits/evidence/c1/c1e/pr/pr-body.md`. `TimeHierarchy/Diagonal.lean` is blob `e8087e57` at `13f52659` and at `0a5878ed`, unchanged by #121. Round 2's bundle includes both. |

**The user's second ruling (2026-10-17): keep R's prefix clause.** After the repair the clause has
no consumer (D's old sketch was its only one). Dropping it would need a statement PR and a regate
of R, which would undo the C1 hosts gate's minor M4 resolution and delay R. It stays, at the cost of
R's early-escape ledger.

**Effect on wave 1:** none. UN uses R's verdict and total-time clause; R's statement is unchanged.

**Design-record corrections** (on the campaign branch):
- `audits/evidence/c1/C1-design.md` §3.6: the prefix clause in its gated form, and the fallback
  sentence replaced by the adopted route.
- D6 and D9 in its §2.5 table: the budget rewrite and the total-time clause.
- `audits/evidence/c1/c1e/C1E-design.md`: the round-2 laws, a fourth deviation (the guessed
  budget), and the freeze count.

## Round 2

- **The head:** `lean/ntime-diag` at `0a5878ed`. It is `2738e9da` (the campaign tip, with #119 and
  #120 merged, merged into `13f52659`) plus the review's patch (`r2-ntimediag.patch`, SHA-256
  `634320d7…`) applied unchanged. `NTimeDiagonalizer.lean` is blob `3f67d257` (round 1:
  `29eaf793`).
- **Checks** (maintainer; `audits/evidence/c1/c1e/pr/r2/`):
  - elaboration against `oleans-lndiag`: 0 errors, the 2 contracts' `sorry`s; the two new lemmas
    use standard axioms;
  - freeze: 20 → 22 publics, the two added. The tool's "UNAUTHORIZED BODY CHANGE:
    exists_diagonalizer" is the docstring: the declaration's code, from the signature to its
    `sorry`, is identical;
  - lint: `Diagonalization/` 0 FAIL, 1 WARN (`EXPCOM`, unrelated), unchanged;
  - screen (the 7-file population): 48 → 49 declarations, 6 → 6 pairs, 1,814 characters, no new
    pair;
  - replay: `replay-lndiag2.sh`, 2 modules, chained from `oleans-lndnf`.
- **Replay passed** (user, 2026-10-17): 2 of 2 at `0a5878ed`, static-equal (2); snapshot
  `oleans-lndiag2`.
- **Gate 40** (folder `40-ntime-diag-statements-r2-gate/`; bundle SHA-256 `3e2b3694…32ef`, 55
  sections; pack `audits/ntime-diag-statements-r2-pack.md`).

### Round 2's result: PASS (0 blockers, 0 majors, 1 minor, 12 notes). The gate is closed.

The findings are in `audits/ntime-diag-statements-r2-findings.md`, verbatim. The maintainer's
review sub-agent rebuilt the bundle byte for byte and verified every finding at `0a5878ed`: all
true, at the auditor's severities (`audits/evidence/c1/c1e/gate40-review.md`).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | Overview text still describes the superseded middle-rung route. | **True, and wider than reported.** **Records:** five edits in `audits/evidence/c1/C1-design.md` (§0 item 5, §1.2, the §2.1 diagram, D6, D8), applied. **`.lean`:** `NDCodeSimulator`'s module Design bullet, in #122 (`6a48b93e`, docstring only). **X1, deferred:** `ntime_hierarchy`'s proof sketch (`NTimeHierarchy.lean:244–264, 274–282, 290–291`) still describes the prefix-clause route. It is UN's in-flight file, so the review's drafted patch is applied when UN integrates, before H's brief. |
| 2–13 | notes | Integrity, the definitions, soundness, completeness, the rewrite's cost, the ledger, `exists_queryTM`, sufficiency, the adversarial checks, the kept clause, the screen and lint, the records. | No action. Note 11, the kept prefix clause, carries into R's continuation brief: proving only the total-time clause is a partial, and the worker escalates rather than weakening the clause. |

**An erratum in round 1's resolutions above:** D's old sketch was not the prefix clause's only
consumer. `ntime_hierarchy`'s sketch also used it (X1). Both now read the total-time clause.

**X2, the import topology (the review; the user's ruling, 2026-10-17).** E-D needs BF
(`Turing.exists_ndAcceptsWithin_decider`), which is stated in `NTimeHierarchy`. H's proof must
import `NTimeDiagonalizer`, so the two files cannot import each other. **Ruling: BF becomes a
hypothesis of `exists_diagonalizer`, after #121 merges.** A small statement PR adds it, and H
supplies it from `exists_ndAcceptsWithin_decider`. It gets its own gate, before E-D's brief.
**Done:** PR #126 (`5333b29b`); gate 45, PASS 0/0/2/10
(`audits/ntime-diag-bf-statements-resolutions.md`).

**X3 (note):** `NTimeDiagonalizer.lean:32` and `:197` still call the middle word R's input; D
now rewrites its budget field first. The review's one-line replacements ride with the X2
statement PR.

**Carry-forward** (the review's section (c)): E-Q and E-D share a file, so they run in sequence.
The fill gates' bundles include every file their lint and screen read.

**#121 is clear to merge** at `0a5878ed`.
