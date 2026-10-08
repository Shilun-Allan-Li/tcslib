<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean :: boolCube1_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The one-bit cube has exactly two points

**Claim.** `(Finset.univ : Finset (BoolCube 1)) = {fun _ => false, fun _ => true}`
— the universe of one-bit inputs is the explicit pair of constant functions.
A `private` enumeration helper.

**Proof.** Immediate from `decide`: `BoolCube 1 = (Fin 1 → Bool)` is a decidable
fintype with two elements. ∎

**Used in.** `BooleanAnalysis.Hypercontractivity.expect_abs_rpow_one_bit` in `TCSlib/BooleanAnalysis/Hypercontractivity/Cube/OneBit.lean`.
