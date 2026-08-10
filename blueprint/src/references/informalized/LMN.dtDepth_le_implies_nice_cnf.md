<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dtDepth_le_implies_nice_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Shallow decision-tree depth gives a nice narrow CNF

**Claim.** If `f : (Fin n → Bool) → Bool` has `dtDepth f ≤ d`, then there is
`ψ : CNF n` with `CNF.width ψ ≤ d`, `CNF.eval ψ x = f x` for all `x`, every
clause `Nodup`, and every clause variable-injective (`l₁.var = l₂.var → l₁ = l₂`
inside a clause).

**Proof.** Two steps, both citations.

1. `(dtDepth_le_implies_small_dnf_cnf f d h).2` supplies a width-`d` CNF `ψ₀`
   equivalent to `f` (read off the depth-`≤ d` decision tree), with no side
   conditions on its clauses.
2. `exists_nice_cnf_of_cnf ψ₀` cleans it into `ψ'` that is `Nodup` and
   variable-injective, with `CNF.width ψ' ≤ CNF.width ψ₀` and the same
   evaluation.
3. Assemble: `le_trans hw' hw₀` for the width and `(heval' x).trans (heval₀ x)`
   for the evaluation. ∎

**Why it exists.** The switching lemma for CNFs
(`switching_bernoulli_dtDepth_cnf`) demands the two clause hygiene conditions,
which a CNF extracted from a decision tree need not satisfy; this lemma is the
bridge from a purely functional hypothesis (`dtDepth f ≤ d`) to a formula that
the switching lemma accepts. It inherits the `sorry` in
`dedupClauseVars_eval_of_not_taut` through `exists_nice_cnf_of_cnf`.

**Used in.** `switching_bernoulli_dtDepth_function`.
