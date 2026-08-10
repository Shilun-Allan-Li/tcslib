<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateSwitching.lean :: all_gates_have_small_cnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Every shallow gate has a narrow CNF

**Claim.** Let `gates : Fin s → DNF n`, `l : ℕ` and `ρ : Restriction n`. If
`dtDepth (restrictFn (gates i).eval ρ) ≤ l` for every `i`, then for every `i`
there is a CNF `ψ : CNF n` with `ψ.width ≤ l` and
`ψ.eval x = restrictFn (gates i).eval ρ x` for all `x`.

**Proof.** Pointwise, with no probability involved: the term
`fun i => restricted_has_small_cnf_of_dtDepth_le _ ρ l (h i)` applies the
single-gate corollary to the hypothesis at index `i`.

**Why it exists.** This is the deterministic half of the gate-switching step: it
converts the "good restriction" conclusion of
`switching_bernoulli_union_bound` (all gates shallow) into the form the circuit
reduction consumes (all gates rewritten as width-`l` CNFs).
