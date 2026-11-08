<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.truth_exPrefix_iff_satisfiable -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Prefixes and Satisfiability

**Claim.** If $m$ has at most $n$ variables, truth of $n$ existential quantifiers from the all-false assignment at index $0$ is equivalent to satisfiability of $m$.

**Proof.** For the forward direction, any true existential prefix yields a satisfying assignment by the result that truth of an all-existential prefix implies satisfiability (satisfiable_of_exPrefix). Conversely, let an assignment satisfy $m$. It agrees with the all-false assignment at every index below $0$, vacuously, and the bound on the number of variables says the $n$ quantified choices cover all variables of $m$. The existential choices can therefore realize this satisfying assignment (exPrefix_of_satisfying).

**Key facts.** `Complexity.QBF.satisfiable_of_exPrefix`, `Complexity.QBF.exPrefix_of_satisfying`.
