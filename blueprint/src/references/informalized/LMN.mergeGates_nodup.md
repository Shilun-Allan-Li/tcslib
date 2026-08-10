<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Term `Nodup` is preserved by gate merging

**Claim.** Let `g₁ : Fin m₁ → DNF n` and `g₂ : Fin m₂ → DNF n`. If every term of
every gate of `g₁` is `Nodup` and likewise for `g₂`, then every term `t` of every
merged gate `mergeGates g₁ g₂ k` (`k : Fin (m₁ + m₂)`) is `Nodup`.

**Proof.** `unfold mergeGates; split <;> [exact h₁ _; exact h₂ _]`: the merged
gate is by definition one of `g₁ _` or `g₂ _`, and `split` on the defining `dite`
turns the goal into exactly `h₁` resp. `h₂` at that index.

**Remark.** Third of the three side-condition transfer lemmas
(`mergeGates_width`, `mergeGates_varInj`, `mergeGates_nodup`), all with the same
two-line proof; they exist to feed the DNF hypotheses of the switching lemma
through the gate-merge step. No current consumer — `LMN.reduce_children`'s `cons`
case is `sorry`.
