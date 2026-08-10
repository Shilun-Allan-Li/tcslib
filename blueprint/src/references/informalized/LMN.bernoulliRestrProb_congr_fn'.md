<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitLayerReduction.lean :: bernoulliRestrProb_congr_fn' -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pointwise-equal functions have the same depth-failure probability

**Claim.** If `f g : (Fin n → Bool) → Bool` satisfy `f x = g x` for all `x`,
then
`bernoulliRestrProb p (fun ρ => dtDepth (restrictFn f ρ) > t) =
bernoulliRestrProb p (fun ρ => dtDepth (restrictFn g ρ) > t)`.
The parameters `p : ℝ` and `t : ℕ` are auto-bound implicits (the file declares
only `variable {n : ℕ}`), not explicit arguments.

**Proof.** `have : f = g := funext h`, then `subst this; rfl` — once the two
functions are literally the same term the two probabilities are the same
expression. ∎

Purely a rewriting convenience: it lets a circuit's `Circuit.eval` be swapped
for the extensionally equal `f` (or for a DNF/CNF normal form) inside a
`bernoulliRestrProb` without touching the probability.

**Used in.** `depth2_circuit_switching_bound`, to replace `f` by `c.eval` before
applying the switching lemma. Note it duplicates
`bernoulliRestrProb_congr_fn` in `LMN/CircuitHelpers.lean`, which states the
same fact with `p` and `t` explicit and proves it via `restrictFn_ext'`.
