<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_width_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width bound on the right half of a merged DNF array

**Claim.** Let `g₁ : Fin m₁ → DNF n`, `g₂ : Fin m₂ → DNF n` and `l : ℕ`. If
`(g₂ k).width ≤ l` for every `k`, then for every `i : Fin m₂`,
`(mergeGates g₁ g₂ (Fin.natAdd m₁ i)).width ≤ l`.

**Proof.** Immediate from `simp [h₂]`.

1. `mergeGates_natAdd` (a `@[simp]` lemma) rewrites the merged gate at the
   right-embedded index to `g₂ i`.
2. The remaining goal `(g₂ i).width ≤ l` is discharged by the hypothesis `h₂`,
   passed to `simp` as a rewrite/closing fact.

**Remark.** Mirror of `mergeGates_width_left`, and like it a granular helper: the
hypothesis constrains only `g₂`, so nothing is assumed about the left array, and
the uniform statement over all of `Fin (m₁ + m₂)` is `mergeGates_width`.
