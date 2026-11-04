<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/CircuitDegree.lean :: pi_coordinate_bad_mul_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# A bad event at one coordinate lifts to the whole dependent product

**Claim.** Let `ι` be a finite type with decidable equality and `β : ι → Type*` a
family of finite types. Fix `i : ι`, a decidable `Bad : β i → Prop` and `C : ℕ`
with `#{b | Bad b} * C ≤ Fintype.card (β i)`. Then

`#{f : (j : ι) → β j | Bad (f i)} * C ≤ Fintype.card ((j : ι) → β j)`.

That is, a "bad fraction at most `1/C`" bound at a single coordinate is preserved
when the other coordinates are added.

**Proof.** Write `Rest := (j : {j // j ≠ i}) → β j.1` and let
`E := piEquivAt i : ((j : ι) → β j) ≃ β i × Rest`.

1. `hsubcard`: an explicit equivalence
   `{f // Bad (f i)} ≃ {b : β i // Bad b} × Rest` built from `E` (its inverse
   uses `E.right_inv` and `congrArg Prod.fst` to re-prove `Bad`) gives, via
   `Fintype.card_subtype`, `Fintype.card_congr` and `Fintype.card_prod`,
   `#{f | Bad (f i)} = #{b | Bad b} * Fintype.card Rest`.
2. `htotal`: `Fintype.card_congr E` and `Fintype.card_prod` give
   `Fintype.card ((j : ι) → β j) = Fintype.card (β i) * Fintype.card Rest`.
3. A `calc` rewrites by `hsubcard`, reassociates with `ring`, applies
   `Nat.mul_le_mul_right` to the hypothesis `hBad`, and closes with `htotal.symm`.

**Used in.** `pi_exists_bad_card_mul_le`, as the per-coordinate input to the union
bound.
