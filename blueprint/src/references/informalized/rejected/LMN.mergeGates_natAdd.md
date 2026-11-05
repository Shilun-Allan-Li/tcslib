<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_natAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Right projection of a merged gate array

**Claim.** For `g₁ : Fin m₁ → α`, `g₂ : Fin m₂ → α` and `i : Fin m₂`,
`mergeGates g₁ g₂ (Fin.natAdd m₁ i) = g₂ i`. Tagged `@[simp]`.

**Proof.** `unfold mergeGates` exposes the `dite` on
`(Fin.natAdd m₁ i).val < m₁`, i.e. on `m₁ + i.val < m₁`.

1. That is false: `have : ¬ (m₁ + i.val < m₁) := by omega`.
2. `simp [this]` takes the `else` branch and simplifies the shifted index
   `⟨m₁ + i.val - m₁, _⟩` back to `i`.

**Used in.** `mergeGates_width_right` and `reidx_eval_mergeGates_right`, which
are discharged by `simp` precisely because this is a `@[simp]` lemma.
