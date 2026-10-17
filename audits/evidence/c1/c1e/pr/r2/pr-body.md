# PR #121's body, as retrieved 2026-10-17 (head `0a5878ed`)

## Round 2 (head `0a5878ed`)

The statement gate's round 1 (`audits/ntime-diag-statements-findings.md`) returned **FAIL 0/1/2/1**.
The resolutions are in `audits/ntime-diag-statements-resolutions.md`. **No statement changes.**

- `2738e9da` merges the campaign tip (#119 and #120 merged). Its Lean for this PR's files is
  unchanged.
- `0a5878ed` applies the review's patch unchanged:
  - **Finding 1 (major), by the user's ruling: the guessed budget.** `exists_diagonalizer`'s sketch
    now guesses a nominal budget `b ≤ g n` in the middle rung and uses R's total-time clause, not
    its prefix clause. R's prefix clause stays in R's statement (the user's second ruling).
  - **Finding 2:** the clock's body allowance (`g n`) and the uniform `K = P + 7 + P'` are
    separated.
  - **Finding 3:** `stage_of_le_two` and `query_of_not_guard`, proved.
- **Checks** (`audits/evidence/c1/c1e/pr/r2/`): 0 errors, the 2 contracts' `sorry`s; freeze 20 → 22
  publics, no statement changed; lint unchanged; screen 48 → 49 declarations, no new pair.
- **Replay passed** (user, 2026-10-17): `replay-lndiag2.sh`, 2 of 2 at `0a5878ed`, 0 failed,
  static-equal (2); snapshot `oleans-lndiag2`.
- **Next:** round 2's statement gate (folder 40). **Not to merge before it closes.**

## Round 1

**C1-E's statements: the lazy diagonalizer.** This is C1-E's statement phase (C1's fill plan `audits/evidence/c1/C1-fill-plan.md`; design note `audits/evidence/c1/c1e/C1E-design.md`), following the user's rulings of 2026-10-17: one stage-query machine, the `Nat.unpair` schedule, and a new module. It states the pieces of [AB09, Theorem 3.2]'s diagonalizer `D` that were still missing, so their fills can run in parallel with wave 1. **It gets a statement gate before it merges.**

**Stacked on #120** (so the replays chain): **merge #118, #119, #120 first.**

New module `Diagonalization/NTimeDiagonalizer` (namespace `Turing.NTimeDiag`):

| Declarations | What | Status |
|---|---|---|
| `budget`, `ladder`, `stage`, `stageCode`, `query` | the P3.3 gate's ladder: `ℓ₀ = 2`, `ℓᵢ₊₁ = 2^{(T*ᵢ)²}` with `T*ᵢ = (f aᵢ + aᵢ + 1)²` and `aᵢ = ℓᵢ + 1`; the stage `ℓᵢ < n ≤ ℓᵢ₊₁`; the scheduled code `(Nat.bits ((Nat.unpair i).1 + 1)).dropLast`; the stage query (top: `true :: ⟨⟨bits T*, α⟩, 1^a⟩`; middle: `false :: ⟨⟨bits (g n), α⟩, 1^{n+1}⟩`) | definitions |
| `budget_eq`, `ladder_zero`, `ladder_succ`, `two_mul_lt_ladder_succ`, `le_ladder`, `ladder_strictMono`, `exists_le_ladder_succ`, `stage_spec`, `stage_eq`, `stageCode_eq`, `stageCode_frequently`, `query_eq`, `acceptLang_mem_NTIME` | their laws; every code recurs at unboundedly many stages; a halting NDTM's bounded language is in `NTIME (g + 1)` | proved |
| `exists_queryTM` | one deterministic machine computes the stage query within `C · (g n + 1)` | sorried (fill E-Q) |
| `exists_diagonalizer` | `D` with uniform time `K · (g n + 1)`, and per code `α` a constant `C`: middle soundness, completeness when `C · (t' + 1) ≤ g n`, and the top flip when `C · 2^{C · (T* + 1)} ≤ n` | sorried (fill E-D) |

The `Diagonalization` facade lists the module and points the normal form to `ClassNP/NDNormalForm` (#120).

**Checks (maintainer, against `oleans-lbapi4`):**

| Check | Result |
|---|---|
| Elaboration | 0 errors; 2 warnings, the two contracts' `sorry`s |
| Axioms | the proved laws: standard only |
| Freeze | a new file: 20 publics, 0 privates |
| Lint | 0 FAIL; `Diagonalization/` 1 WARN, as before (check 8 is satisfied for the new definitions) |
| Screen (7 files) | 40 → 48 declarations, 6 → 6 pairs: none new |

**Replay (user):** `replay-lndiag.sh`, the new module and the facade (2 modules), from `oleans-lndnf` (#120's replay).

🤖 Generated with [Claude Code](https://claude.com/claude-code)


