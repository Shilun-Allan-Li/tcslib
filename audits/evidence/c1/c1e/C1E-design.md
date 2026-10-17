# C1-E's statement phase: the diagonalizer (maintainer draft, 2026-10-17)

**What it is.** C1's design (§2.5) lists the diagonalizer `D`'s pieces, D1–D9, and the P3.3 gate's
round 2 pins its capped locator, its clock reserve and the chain (`audits/ch3-p33-r2-findings.md`
§§1–5). None of the missing pieces is stated yet. This phase states them as contracts, so their
fills can run in parallel. The user ruled on 2026-10-17 that it starts now (C1's fill plan,
question 4).

**The unit:** a new module `Diagonalization/NTimeDiagonalizer.lean`. The draft is
`NTimeDiagonalizer.lean.txt`. It elaborates against `oleans-lbapi4` with 0 errors and the 2
contracts' `sorry`s (`draft.out`). Every proved lemma uses standard axioms only.

| Declaration | Kind | Status |
|---|---|---|
| `budget`, `ladder`, `stage`, `stageCode`, `query` (namespace `Turing.NTimeDiag`) | pure definitions: the ladder `ℓ₀ = 2`, `ℓᵢ₊₁ = 2^{(T*ᵢ)²}` with `T*ᵢ = (f aᵢ + aᵢ + 1)²`; the stage `ℓᵢ < n ≤ ℓᵢ₊₁`; the scheduled code; the stage query | — |
| `ladder_zero`, `ladder_succ`, `two_mul_lt_ladder_succ`, `le_ladder`, `ladder_strictMono`, `exists_le_ladder_succ`, `stage_spec`, `stage_eq`, `stageCode_frequently`, `query_eq` | the stages' laws | proved |
| `acceptLang_mem_NTIME` | a halting NDTM's bounded language is in `NTIME (g + 1)` | proved |
| `exists_queryTM` | one deterministic machine computes the stage query within `C · (g n + 1)` | sorried: fill E-Q |
| `exists_diagonalizer` | `D`: uniform time `K · (g n + 1)`; per code `α` a constant `C`; middle soundness, and completeness under `C · (t' + 1) ≤ g n`; the top flip when `C · 2^{C · (T* + 1)} ≤ n` | sorried: fill E-D |

**How the design's pieces map:**
- **D1, D2, D4, D5** (the unary check, `bits (g n)`, the locator, the materialization) are internal to
  `exists_queryTM`. Its machine computes the pure `query` and is called on the native input by
  `Turing.FinTM.exists_inputCallTM` (proved).
- **D3, D6, D7, D8** (the guess, the middle and top rungs, `D ∈ NTIME (g + 1)`) are
  `exists_diagonalizer`'s fill, the assembly. `acceptLang_mem_NTIME` gives D8 from its time clause.
- **D9 and H0** (the chain and the inclusion) are `ntime_hierarchy`'s fill. That fill is pure, from
  `exists_diagonalizer`, the normal form, `NDMachineCode.decode_encode` and the stage lemmas.
- **P and S** (`ntime_hierarchy_of_pos`, the showcase) are already in wave 1's UN brief.

**Why the diagonalizer's contract has this form.** Its clauses are exactly the inputs of the gate's
chain:
- the middle comparison (§4): soundness, and completeness when `C · (t' + 1) ≤ g n`, applied at
  `t' = C₁(c₀ f(n + 1) + 1)` with `A*`;
- the top budget (§5): the flip when `C · 2^{C · (T* + 1)} ≤ n`;
- the uniform reserve (§3): `K`.

The per-code `C` comes after `∀ α`, so every threshold precedes the stage selection (the gate's fix
of round-1 major 1). The capped locator's timeout reasoning stays inside `exists_queryTM`'s fill,
because `query` is defined mathematically.

## Deviations from the design, for the gate

1. **The packaging.** The design has separate contracts for the locator (D4) and the materializer
   (D5). Here they, and `g`'s witness, are internal to one deterministic machine computing a pure
   function: one fill instead of three. The locator's arithmetic rows (a numeric `≤`, fixed-degree
   binary arithmetic, the `⌊log₂⌋` comparison, the power-of-two test, `Nat.unpair` on binary
   words, the unranking) are that fill's private leaves, with promotion requests (policy's route).
2. **The schedule.** The design suggested `j = ν₂(i + 1)` and left the pairing open. Here
   `j = (Nat.unpair i).1`, Mathlib's pairing: no new import, the same recurrence property (proved),
   and polylog machine cost either way.
3. **The home.** A new module, so `NTimeHierarchy` (owned by wave 1's UN brief) is untouched.
   `ntime_hierarchy`'s fill adds the import later.

## After the gate (sizes ESTIMATE)

- **E-Q,** `exists_queryTM`: 2–4k lines (the locator 1.5–3k, the writer 300–600, the glue).
- **E-D,** `exists_diagonalizer`: 1–2k lines, citing E-Q, W, R, BF and the step clock as statements.
- **H,** `ntime_hierarchy`: 1–2k lines, pure, after the UN brief integrates (the same file).

E-Q and E-D can run in parallel with wave 1.
