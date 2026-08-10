<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: mergeGates_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Width bounds are preserved by gate merging

**Claim.** Let `g₁ : Fin m₁ → DNF n`, `g₂ : Fin m₂ → DNF n` and `l : ℕ`. If
`(g₁ k).width ≤ l` for all `k` and `(g₂ k).width ≤ l` for all `k`, then
`(mergeGates g₁ g₂ k).width ≤ l` for every index `k : Fin (m₁ + m₂)`.

**Proof.** `unfold mergeGates; split <;> [exact h₁ _; exact h₂ _]`.

1. `unfold mergeGates` exposes the defining `dite` on `k.val < m₁`.
2. `split` produces the two branches; each is literally an instance of the
   corresponding hypothesis at the branch's index, closed by `exact h₁ _` and
   `exact h₂ _`. No arithmetic about the shifted index is needed, since the
   statement is index-agnostic.

**Used in.** Together with `mergeGates_varInj` and `mergeGates_nodup`, this is
the form needed to re-establish the three DNF side conditions of
`LMN.reduce_children` (`CircuitTreeManip.lean`) after merging; that proof's
`cons` case is still `sorry`, so the lemma has no current consumer.
