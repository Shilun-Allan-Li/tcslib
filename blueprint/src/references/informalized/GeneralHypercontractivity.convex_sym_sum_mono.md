<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: convex_sym_sum_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Symmetric sums of a convex function grow with the spread

**Claim.** Let `f : ℝ → ℝ` be convex on `Set.Ici 0` and let `0 ≤ x ≤ y ≤ 1`.
Then `f (1 + x) + f (1 - x) ≤ f (1 + y) + f (1 - y)`. Widening the symmetric
pair `1 ± x` to `1 ± y` (both pairs lying in `[0, 2] ⊆ Ici 0`) can only increase
the sum.

**Proof.** Two cases on `x < y`.

1. If `x = y` (the `¬ x < y` branch), `le_antisymm hxy (not_lt.mp hxy')`
   rewrites the goal to an identity.
2. If `x < y`, compare two slopes of `f` based at `1 - y`:
   - `ConvexOn.secant_mono` gives
     `(f (1-x) - f (1-y)) / (y - x) ≤ (f (1+y) - f (1-y)) / (2*y)`,
     after rewriting `1 - x - (1 - y) = y - x` and `1 + y - (1 - y) = 2*y`.
   - `ConvexOn.slope_mono_adjacent` on the ordered points
     `1 - y < 1 + x < 1 + y` gives the companion slope inequality.
3. Clearing the denominators of both (`div_le_div_iff₀`, all of `y - x`, `2*y`
   positive) and feeding the products to `nlinarith` yields the claim.

**Note.** A standalone convexity fact stated for the `1 ± t` family that the
two-point inequalities in this file use; as written it has no consumers anywhere
in the repository (see report).
