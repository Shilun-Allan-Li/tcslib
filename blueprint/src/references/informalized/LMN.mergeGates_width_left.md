<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_width_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width bound on the left half of a merged DNF array

**Claim.** Let `g₁ : Fin m₁ → DNF n`, `g₂ : Fin m₂ → DNF n` and `l : ℕ`. If
`(g₁ k).width ≤ l` for every `k`, then for every `i : Fin m₁` the merged gate at
the left-embedded index satisfies
`(mergeGates g₁ g₂ (Fin.castAdd m₂ i)).width ≤ l`.

**Proof.** Immediate from `simp [h₁]`: the `@[simp]` lemma `mergeGates_castAdd`
rewrites the gate to `g₁ i`, and the hypothesis `h₁` closes the resulting
`(g₁ i).width ≤ l`.

**Remark.** A deliberately granular helper — the uniform statement over all of
`Fin (m₁ + m₂)` is `mergeGates_width`; this specialized form exists so callers
holding a left-embedded index need no case split.
