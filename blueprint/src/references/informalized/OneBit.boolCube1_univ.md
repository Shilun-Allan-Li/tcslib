<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/OneBit.lean :: boolCube1_univ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The one-bit cube has exactly two points

**Claim.** `(Finset.univ : Finset (BoolCube 1)) = {fun _ => false, fun _ => true}`
— the universe of one-bit inputs is the explicit pair of constant functions.
A `private` enumeration helper.

**Proof.** Immediate from `decide`: `BoolCube 1 = (Fin 1 → Bool)` is a decidable
fintype with two elements. ∎

**Used in.** `expect_abs_rpow_one_bit`, to rewrite an expectation over `BoolCube 1`
into a two-term sum via `Finset.sum_pair boolCube1_ne`. Its companion
`finsetFin1_univ` does the same for `Finset (Fin 1) = {∅, {0}}` on the Fourier side.
