<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTMEquiv.lean :: Randomized.eff_boolVerifier_of_test -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Efficiency from a Polynomial-Time Test

**Claim.** If a polynomial-time Boolean test on paired inputs agrees with $M(x,r)$, then the verifier that returns $M(x,r)$ as its optional Boolean decision is efficient.

**Proof.** Take as the accepting language the set of strings $z$ on which $t(z)$ is true. The polynomial-time computation of the one-symbol output $[t(z)]$ puts this language in polynomial time (`Complexity.mem_P_of_test`); its complement is also in polynomial time (`Complexity.compl_mem_P`). On the encoding of $(x,r)$, the assumed identity $t(\langle x,r\rangle)=M(x,r)$ identifies acceptance with output true and rejection with output false. Thus these two languages provide the required efficient verifier certificates.

**Key facts.** `Complexity.mem_P_of_test`, `Complexity.compl_mem_P`.
