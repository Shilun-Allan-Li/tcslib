<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/AlgCircuit.lean :: Randomized.AlgCircuit.totalDegree_toMvPolynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for circuit polynomials

**Claim.** For an arithmetic circuit $C$, the total degree of its polynomial over $\mathbb{Z}$ is at most $2^{\mathrm{size}(C)}$.

**Proof.** The polynomial represented by $C$ is its execution on the formal input variables, read at the output position given by the circuit size minus one. Apply the execution degree bound at that position (`Randomized.AlgCircuit.totalDegree_run_le`) to obtain the stated upper bound, since the gate-list length is the circuit size.

**Key facts.** `Randomized.AlgCircuit.totalDegree_run_le`.
