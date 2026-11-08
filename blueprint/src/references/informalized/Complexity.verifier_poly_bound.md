<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.verifier_poly_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial bound test

**Claim.** For any $C,c\in\mathbb{N}$, the function that outputs the one-bit indicator of whether a decoded pair $(a,b)$ satisfies $|b|\le C(|a|+1)^c$ is polynomial-time computable, returning $0$ when decoding fails.

**Proof.** The machine construction for checking a pair's second-component length against a polynomial bound gives a machine computing the stated test, with running time bounded by a constant times $(n+1)^{c+1}$ on inputs of length $n$ (\texttt{Turing.FinTM.computesFunInTime_pairLenCheck}). The test in the definition of the present function is exactly that pair-decoding check, including the value false when decoding fails. Hence it is polynomial-time computable.

**Key facts.** `Turing.FinTM.computesFunInTime_pairLenCheck`.
