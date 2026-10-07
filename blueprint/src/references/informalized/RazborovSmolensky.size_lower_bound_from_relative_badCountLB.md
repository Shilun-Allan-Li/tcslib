<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/SmolenskyAlgebra.lean :: size_lower_bound_from_relative_badCountLB -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Relative-error form of the size lower bound

**Claim.** Same setup as `size_lower_bound_from_badCountLB` (circuit `F` over gates
`ACp_GateOps p`, computing `MOD q` exactly), but with the low-degree lower bound stated with
error count `δ * 2 ^ n`: if
`LowDegreeBadCountLB (modQTarget) (circuitDegreeBound p ℓ F.depth) (δ * 2 ^ n)` holds, then
`δ * 2 ^ ℓ ≤ F.size`.

**Proof.** Three `have`s.

1. `size_lower_bound_from_badCountLB` applied with `E := δ * 2 ^ n` gives
   `(δ * 2 ^ n) * 2 ^ ℓ ≤ F.size * 2 ^ n`.
2. `simpa [mul_assoc, mul_left_comm, mul_comm]` reassociates this into
   `(δ * 2 ^ ℓ) * 2 ^ n ≤ F.size * 2 ^ n`.
3. `positivity` gives `0 < 2 ^ n`, so `Nat.le_of_mul_le_mul_right` cancels the common factor.

**Remark.** `δ` here is a natural number, so the "fraction" is expressed as the absolute
count `δ * 2 ^ n` rather than a rational error rate.
