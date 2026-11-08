<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clTemplate_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds and correctness of the chosen table

**Claim.** The chosen CNF table for $p$ uses at most $\ell$ variables, has at most $2^\ell$ clauses, every clause has at most $\ell$ literals, and evaluates under every assignment to $p$ applied to that assignment's first $\ell$ bits.

**Proof.** The chosen table is selected from the existence theorem for Boolean functions, which supplies a CNF satisfying all four stated properties. The specification follows directly from the defining property of this choice (`Complexity.exists_cnf_boolFun`).

**Key facts.** `Complexity.exists_cnf_boolFun`.
