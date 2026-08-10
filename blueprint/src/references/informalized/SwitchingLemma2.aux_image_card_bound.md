<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: aux_image_card_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# At most `(4w)^d` aux-strings per encoding fiber

**Claim.** Let `f : DNF n` with `f.width ≤ w`, let `d : ℕ`, and fix a target
restriction `γ`. Consider the bad restrictions `ρ` (i.e. `IsBadRestriction f.eval
d ρ`) whose Razborov encoding has first component `γ`, and take the image of that
set under `ρ ↦ (razborovEncode f w d ρ).2` (the aux string). Then the image has at
most `(4 * w) ^ d` elements.

**Proof.** `private` helper; a counting bound obtained by injecting aux strings
into a finite function type.

1. **Case `w = 0`.** `f.width ≤ 0` forces every term of `f` to be `[]`
   (`term_length_le_width`, `List.length_eq_zero_iff`). An empty term is
   `fixedBy` every restriction, so `fixedTerm_implies_dtDepth_zero` gives
   `dtDepth (restrictFn f.eval ρ) = 0`; if `f = []` instead,
   `killedAll_implies_dtDepth_zero` gives the same. Either way no `ρ` is bad, the
   filter is `∅` (`Finset.eq_empty_iff_forall_notMem`), and
   `Finset.image_empty` makes the cardinality `0`.
2. **Case `w > 0`.** `exists_aux_injection` supplies
   `g : List (ℕ × Bool) → (Fin d → Fin w × Bool × Bool)` that is injective on the
   image set `S` (it parses each aux string into `d` triples
   `(position, direction, is-last-of-clause)`).
3. `Finset.card_image_of_injOn` turns `S.card` into `(S.image g).card`, which is at
   most `Finset.card_univ = Fintype.card (Fin d → Fin w × Bool × Bool)` by
   `Finset.card_le_card (Finset.subset_univ _)`.
4. That cardinality is `(w · 2 · 2) ^ d = (4 * w) ^ d`
   (`Fintype.card_fun`, `Fintype.card_prod`, `ring`).

**Used in.** `fiber_bound`, which first drops the `IsRestriction s` conjunct and
uses `razborovEncode_injective` to identify the fiber with its aux image.
