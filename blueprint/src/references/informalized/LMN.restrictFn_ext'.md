<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: restrictFn_ext' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Restriction of pointwise-equal functions

**Claim.** For `f g : (Fin n → Bool) → Bool` with `f x = g x` for every `x`, and
any restriction `ρ : Restriction n`, the restricted functions are equal:
`restrictFn f ρ = restrictFn g ρ`.

**Proof.** One line, `ext x; simp [restrictFn]; exact h _`: after `ext` the goal
is `f (ρ.extend x) = g (ρ.extend x)`, which is the hypothesis at the point
`ρ.extend x`. Extensionality is needed only because `restrictFn f ρ` is itself a
function (`fun x => f (ρ.extend x)`), not a Boolean.

**Used in.** `bernoulliRestrProb_congr_fn`, immediately below it in the same
file, which rewrites with this lemma to conclude that pointwise-equal functions
have the same `bernoulliRestrProb` of exceeding decision-tree depth `t`. Nothing
outside `CircuitHelpers.lean` calls it directly.
