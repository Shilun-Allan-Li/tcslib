<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecGateCNF_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate CNF specification

**Claim.** The chosen gate CNF has cost at most $2^{3k+7}(3k+8)$ and, on every assignment, evaluates to the gate value obtained by reading the wired variables.

**Proof.** By the gate-CNF existence theorem (`Complexity.codecGate_cnf`), there is a formula satisfying both the stated cost bound and the evaluation identity. The definition of `codecGateCNF` selects that formula. Its existence theorem supplies both conjuncts of the specification, so the selected formula has the required cost and evaluation behavior.

**Key facts.** `Complexity.codecGate_cnf`.
