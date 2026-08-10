<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: bernoulliRestrProb_congr_fn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pointwise-equal functions have the same depth-failure probability

**Claim.** If `f g : (Fin n → Bool) → Bool` satisfy `f x = g x` for all `x`, then
for every `p : ℝ` and `t : ℕ`,
`bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) =
bernoulliRestrProb p (fun ρ => dtDepth (restrictFn g ρ) > t)`.
Both `p` and `t` are explicit arguments here.

**Proof.** Two steps, one line: `congr 1; ext ρ; rw [restrictFn_ext' h]`.

1. `congr 1` reduces equality of the two `bernoulliRestrProb` applications to
   equality of the two event predicates, and `ext ρ` fixes a restriction `ρ`.
2. `restrictFn_ext' h ρ : restrictFn f ρ = restrictFn g ρ` (proved in the same
   file by `ext x; simp [restrictFn]; exact h _`, i.e. both sides are
   `f (ρ.extend x)` and `g (ρ.extend x)`), so rewriting closes the goal. ∎

**Anomaly.** This lemma has no callers anywhere in the library. The version
actually used is `bernoulliRestrProb_congr_fn'` in
`LMN/CircuitLayerReduction.lean`, which states the same fact with `p` and `t`
auto-bound and proves it by `funext` + `subst`. Even
`switching_bernoulli_dtDepth_dnf_general` / `..._cnf_general`, sitting a few
lines below in this file, do the same rewriting by hand with
`rw [show f.eval = … from funext …]` instead of calling this lemma.
