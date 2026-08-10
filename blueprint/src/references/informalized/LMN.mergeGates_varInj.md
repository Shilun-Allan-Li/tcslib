<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_varInj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Per-term variable injectivity is preserved by gate merging

**Claim.** Let `g₁ : Fin m₁ → DNF n` and `g₂ : Fin m₂ → DNF n`. Suppose that in
every gate of `g₁`, and in every gate of `g₂`, any two literals of a common term
that agree on `.var` are equal — i.e. `∀ k, ∀ t ∈ gᵢ k, ∀ l₁ ∈ t, ∀ l₂ ∈ t,
l₁.var = l₂.var → l₁ = l₂`. Then the same holds for every gate
`mergeGates g₁ g₂ k`, `k : Fin (m₁ + m₂)`.

**Proof.** `unfold mergeGates; split <;> [exact h₁ _; exact h₂ _]` — after
unfolding the defining `dite`, `split` leaves one goal per branch and each is an
instantiation of `h₁` resp. `h₂` at that branch's index.

**Remark.** This is the "no variable repeated in a term" hypothesis carried by
the counting switching lemma (`SwitchingLemma2.switching_lemma`); merging gate
arrays must not destroy it. Currently unused: the intended consumer,
`LMN.reduce_children`, has a `sorry`'d `cons` case.
