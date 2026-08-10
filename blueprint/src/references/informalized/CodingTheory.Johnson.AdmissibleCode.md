<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: AdmissibleCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# `AdmissibleCode n d w`: distance-`d`, weight-`≤ w` binary codes

**Definition.** `AdmissibleCode n d w C` is the conjunction of two conditions on
a finite set of bit vectors `C : Finset (BitVec n)`:

1. **Minimum distance.** `∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hdist x y` — any two
   distinct codewords differ in at least `d` coordinates, where `hdist` counts
   the coordinates on which they disagree.
2. **Weight ceiling.** `∀ x ∈ C, wt x ≤ w` — every codeword has Hamming weight
   at most `w`, where `wt x` counts the coordinates where `x` is `true`.

**Remark.** The weight condition is an upper bound, not the equality `wt x = w`
of the classical constant-weight setting; the Johnson argument in this file only
ever needs `wt x ≤ w` (it enters through `inner_shifted_le_expr` as an upper
bound on `2 * wt x`).

**Used in.** As the packaging hypothesis of
`binary_johnson_card_bound_of_admissible`, which destructures it with `rcases`
into the two hypotheses of `binary_johnson_card_bound`; it is also the predicate
filtered on in the definition of `A0 n d w`.
