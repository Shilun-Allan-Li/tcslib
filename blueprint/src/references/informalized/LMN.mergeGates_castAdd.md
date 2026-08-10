<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_castAdd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Left projection of a merged gate array

**Claim.** For `g₁ : Fin m₁ → α`, `g₂ : Fin m₂ → α` and `i : Fin m₁`,
`mergeGates g₁ g₂ (Fin.castAdd m₂ i) = g₁ i`. Tagged `@[simp]`.

**Proof.** After `unfold mergeGates` the goal is a `dite` on
`(Fin.castAdd m₂ i).val < m₁`; that value is `i.val`, so the condition holds by
`i.isLt` and `simp [i.isLt]` selects the `then` branch and closes the residual
index equality `⟨i.val, _⟩ = i`.

**Remark.** This and `mergeGates_natAdd` are the only facts about `mergeGates`
that downstream proofs need in rewriting form; being `simp` lemmas they are what
makes the one-line proofs of `mergeGates_width_left` and
`reidx_eval_mergeGates_left` go through.
