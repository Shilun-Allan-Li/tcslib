<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.a3n_poly_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Functions Are Polynomial-Time Computable

**Claim.** For every finite Boolean word $w$, the function returning $w$ on every input is polynomial-time computable.

**Proof.** A machine can output the fixed word $w$ in time bounded linearly by the input length plus one (Turing.FinTM.computesFunInTime_const). Apply the implication from linear-time computability to polynomial-time computability (Complexity.a3n_poly_linear).

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Complexity.a3n_poly_linear`.
