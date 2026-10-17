# External audit pack — C1-E's statements: the lazy diagonalizer (PR #121, a statement gate)

Campaign: the Arora-Barak chapters 3-4 plan, C1 (the nondeterministic time hierarchy, [AB09, Theorem
3.2] [Coo72]). C1's design (`audits/evidence/c1/C1-design.md` §2.5) lists the diagonalizer `D`'s
pieces. The P3.3 statement gate's round 2 (`audits/ch3-p33-r2-findings.md` §§1–5) pinned its capped
locator, its clock reserve and the chain. None of the missing pieces was stated. This unit states
them, so that their fills (E-Q, E-D) and the hierarchy's own fill (the chain) can run in parallel.
- **The user's rulings** (2026-10-17; `audits/evidence/c1/c1e/C1E-design.md`):
  - one deterministic machine for the stage query, rather than separate locator and materializer
    contracts;
  - the schedule by Mathlib's `Nat.unpair`;
  - a new module.
- **The head:** `lean/ntime-diag` at `13f52659`: one commit (`2ff6cc0c`) on #120's head, merged with
  #119's later commits. Its Lean diff from #120's head `6d18902f` is two files.

| Declarations (new `Diagonalization/NTimeDiagonalizer`, namespace `Turing.NTimeDiag`) | Status |
|---|---|
| `budget`, `ladder`, `stage`, `stageCode`, `query` (definitions) | — |
| `budget_eq`, `ladder_zero`, `ladder_succ`, `two_mul_lt_ladder_succ`, `le_ladder`, `ladder_strictMono`, `exists_le_ladder_succ`, `stage_spec`, `stage_eq`, `stageCode_eq`, `stageCode_frequently`, `query_eq`, `acceptLang_mem_NTIME` | proved |
| `exists_queryTM`: one deterministic machine computes `query f g` within `C·(g n + 1)` | sorried (fill E-Q) |
| `exists_diagonalizer`: the machine `D`, in the per-rung form the chain reads | sorried (fill E-D) |

The `Diagonalization` facade lists the module, and its module list points the normal form to
`ClassNP/NDNormalForm` (#120).

- **Evidence:** `audits/evidence/c1/c1e/`: the design note with the rulings, the draft and its
  elaboration, and `pr/` (the logs, the freeze, the lint, the screen, the replay closure and script,
  the patch).

## Brief for the auditor

1. **The stages are the gate's.**
   - Is `ladder` exactly the round-2 recurrence: `ℓ₀ = 2`, `aᵢ = ℓᵢ + 1`, `T*ᵢ = (f aᵢ + aᵢ + 1)²`,
     `ℓᵢ₊₁ = 2^{(T*ᵢ)²}`?
   - Is `stage` the bracket `ℓᵢ < n ≤ ℓᵢ₊₁` for `n ≥ 3`?
   - Does `stageCode` satisfy the fixed-code schedule's requirement: every code at unboundedly many
     stages (`stageCode_frequently`)?
2. **The stage query.** Is `query f g` the word each rung must simulate?
   - At the top `n = ℓᵢ₊₁`: `⟨⟨bits T*, α⟩, 1^{ℓᵢ + 1}⟩`, for BF.
   - In the middle: `⟨⟨bits (g n), α⟩, 1^{n + 1}⟩`, for the interpreter core.
   - The flag, and `[]` off unary inputs of length at least 3.
3. **`exists_queryTM` is true.** The bound `C·(g n + 1)` must be achievable for every
   time-constructible `f`, `g`. Check it against the gate's §2 ledger: the capped locator is
   `O(n + log³ n)`, and `n ≤ g n`. Watch for any rung or length at which computing the query
   requires time beyond that, in particular the binary arithmetic on `T*` and the materialization of
   `1^{n+1}` and `1^{ℓᵢ+1}`.
4. **`exists_diagonalizer` is true, and sufficient.**
   - **True:** is each clause achievable by the route in its sketch (guess, interpreter core, BF,
     the step clock with the uniform reserve `K ≥ P + 2`), for a single uniform `K` and a per-code
     `C`? Consider the middle soundness (an accept implies the coded acceptance of `1^{n+1}` within
     `g n`), the middle completeness (`C·(t' + 1) ≤ g n`), the top flip (`C·2^{C·(T* + 1)} ≤ n`) and
     uniform halting.
   - **Not vacuous:** could a trivial `D` satisfy it? For instance one rejecting everything, or a
     choice of `C` that never meets the hypotheses.
   - **Sufficient:** together with the normal form, `NDMachineCode.decode_encode` and the stage
     lemmas, does it give the gate's chain (§§4–5): the middle equivalence at the fixed `A*`, the
     bottom transfer, the top flip, all thresholds before the stage choice? `acceptLang_mem_NTIME`
     gives the time half.
5. **The deviations, for the gate:**
   - one query machine instead of the design's separate locator (D4) and materializer (D5)
     contracts;
   - `Nat.unpair` instead of the design's suggested 2-adic pairing.
6. **The proved lemmas** are correct and use standard axioms; check `stage_eq`'s uniqueness argument
   and `stageCode_frequently`'s witness.
7. **Records:** do the design note, this pack and the PR body agree with the evidence?

## Repository-side attestations (verify or challenge)

- **Elaboration** (against `oleans-lbapi4`): 0 errors; 2 warnings, the two contracts' `sorry`s. The
  proved lemmas use standard axioms only (`draft.out`, `pr/logs/`).
- **Freeze:** a new file with 20 publics and 0 privates.
- **Lint:** 0 FAIL; `Diagonalization/` has 1 WARN, as before. Check 8 is satisfied for the new
  definitions.
- **Screen** (7 files): 40 → 48 declarations, 6 → 6 pairs, none new.
- **Replay:** `replay-lndiag.sh`, 2 modules, chained from `oleans-lndnf` (#120's replay). **Passed
  (user, 2026-10-17):** 2 of 2 at `13f52659`, 0 failed (`pr/replay-lndiag.log`); the sorry counts equal
  a static count (0 mismatches, 2; `pr/replay-lndiag-static.txt`). The snapshot `oleans-lndiag` is the
  tip plus #119, #120 and #121.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ntime-diag-statements-findings.md`. The gate closes when it has zero blockers and zero
majors.
