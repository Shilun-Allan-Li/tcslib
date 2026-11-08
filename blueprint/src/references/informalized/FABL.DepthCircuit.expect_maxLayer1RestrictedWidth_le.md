<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.DepthCircuit.expect_maxLayer1RestrictedWidth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected restricted first-layer width bound

**Claim.** For a circuit $C$, the expected maximum restricted width of its first-layer gates under a half-random restriction is at most the initial restriction width associated with the number of first-layer gates.

**Proof.** First bound the expected maximum blocked restricted width. For each first-layer term, its blocked restricted width has exponential moment at most $2$ under a half-random restriction. The general maximum estimate for random variables with these moment bounds therefore gives an expected maximum at most $\log_2(m+1)+2$, where $m$ is the number of first-layer gates. The circuit's maximum blocked width is exactly this maximum over gates.

For each restriction, the actual restricted width is at most five times the blocked width plus four. Monotonicity of expectation transfers this pointwise bound to expectations. Linearity of expectation then gives an upper bound of five times the expected maximum blocked width plus four, which simplifies to $5(\log_2(m+1)+2)+4$. By the definitions of the circuit influence logarithm and the initial restriction width, this is the stated bound.

**Key facts.** `FABL.DNFTerm.expect_two_pow_blockedRestrictedGateWidth_le_two`, `FABL.expect_sup_le_clog_add_two_of_twoPow_le_two`, `FABL.DepthCircuit.maxLayer1RestrictedWidth_le_blocked`, `FABL.expectRandomRestriction_mono`, `FABL.expectRandomRestriction_const_mul`, `FABL.expectRandomRestriction_add`, `FABL.expectRandomRestriction_const`.
