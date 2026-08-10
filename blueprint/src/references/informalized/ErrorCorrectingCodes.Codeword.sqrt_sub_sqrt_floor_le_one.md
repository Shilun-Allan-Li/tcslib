<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/Entropy.lean :: sqrt_sub_sqrt_floor_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Square root moves by at most one under flooring

**Claim.** For `x : ℝ` with `0 ≤ x`, `√x - √(⌊x⌋₊) ≤ 1`.

**Proof.** Compare squares, using `x - ⌊x⌋₊ ≤ 1`.

1. `suffices` it suffices to prove `‖√x - √⌊x⌋₊‖ ≤ ‖(1:ℝ)‖`: the difference is
   nonnegative because `⌊x⌋₊ ≤ x` (`Nat.floor_le`) and `Real.sqrt_le_sqrt`, so
   `abs_of_nonneg` strips the absolute value.
2. `sq_le_sq.1` reduces the norm inequality to
   `(√x - √⌊x⌋₊)² ≤ 1²`. Expanding with `sub_sq` and `Real.sq_sqrt` (twice) gives
   the goal `x - 2·√x·√⌊x⌋₊ + ⌊x⌋₊ ≤ 1`.
3. `calc` step one replaces `√x·√⌊x⌋₊` by the smaller `√⌊x⌋₊·√⌊x⌋₊`: from
   `√⌊x⌋₊ ≤ √x` (`Real.sqrt_le_sqrt (Nat.floor_le hx)`) via
   `mul_le_mul_iff_right₀`/`mul_le_mul_iff_left₀`, with the degenerate case
   `⌊x⌋₊ = 0` split off by `by_cases` (both sides collapse to `0`).
4. The remaining chain is arithmetic: `√⌊x⌋₊·√⌊x⌋₊ = ⌊x⌋₊` (`simp`), so the bound
   becomes `x - 2⌊x⌋₊ + ⌊x⌋₊ = x - ⌊x⌋₊` (`ring_nf`), and
   `linarith [Nat.sub_one_lt_floor x]` (i.e. `x - 1 < ⌊x⌋₊`) gives `≤ 1`. ∎

**Note.** A standalone analytic helper (not `private`); it is the `√`-analogue of
`x - ⌊x⌋ < 1`, kept separate because the squaring argument is the only nontrivial
part.
