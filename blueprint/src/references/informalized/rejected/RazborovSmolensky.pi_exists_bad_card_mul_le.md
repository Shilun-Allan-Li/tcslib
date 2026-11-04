<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: pi_exists_bad_card_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Union bound over the coordinates of a dependent product

**Claim.** Let `ι` be a finite type with decidable equality, `β : ι → Type*` a
family of finite types, `Bad : ∀ i, β i → Prop` decidable and `C : ℕ`. If
`#{b : β i | Bad i b} * C ≤ Fintype.card (β i)` for every `i`, then

`#{f : (i : ι) → β i | ∃ i, Bad i (f i)} * C ≤ Fintype.card ι * Fintype.card ((i : ι) → β i)`.

The loss is exactly the number of coordinates — a union bound, not an
independence argument.

**Proof.**

1. Name the target set `Target` and the single-coordinate sets
   `Coord i := {f | Bad i (f i)}`.
2. `hcover`: `Target ⊆ Finset.univ.biUnion Coord`, since a witness `i` from
   `Finset.mem_filter` supplies membership via `Finset.mem_biUnion`.
3. `hcard`: `Finset.card_le_card hcover` composed with `Finset.card_biUnion_le`
   gives `Target.card ≤ ∑ i, (Coord i).card`.
4. A `calc` multiplies by `C` (`Nat.mul_le_mul_right`), distributes with
   `Finset.sum_mul`, bounds each summand by `Fintype.card ((i : ι) → β i)` using
   `pi_coordinate_bad_mul_le` under `Finset.sum_le_sum`, and `simp` evaluates the
   constant sum.

**Used in.** `stepLayerFamily`, where `ι` is the set of gates in the new layer and
`Bad u` is "the seed for gate `u` makes its approximating polynomial wrong"; the
factor `Fintype.card ι` is what makes the total error grow by one layer's gate
count.
