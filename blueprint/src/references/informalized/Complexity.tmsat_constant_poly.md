<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_constant_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant functions are polynomial-time

**Claim.** For every bit string $w$, the function sending every bit string to $w$ is polynomial-time computable.

**Proof.** The constant-output machine theorem (`Turing.FinTM.computesFunInTime_const`) supplies a machine that outputs $w$ on every input within $C(|x|+1)$ steps for some constant $C$. This is a polynomial time bound with exponent $1$, so the function is polynomial-time computable.

**Key facts.** `Turing.FinTM.computesFunInTime_const`.
