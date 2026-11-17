<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.signAndFunctionTester_parity_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity Acceptance Probability

**Claim.** For a coordinate set $S$, the sign-AND tester accepts the parity function with probability $\frac12+\left(\frac34-\frac14(-1)^{|S|}\right)2^{-|S|}$.

**Proof.** The tester’s acceptance probability is the expectation of the acceptance indicator over independent uniform inputs (\texttt{signAndFunctionTester\_acceptanceProbability}). For signs $a,b,c$, that indicator equals $(2+c+ac+bc-abc)/4$ when $c$ is the claimed output (\texttt{signAnd\_indicator}). Apply this identity with $a$ and $b$ the parity values at the two inputs and $c$ the parity value at their coordinatewise AND, then take expectations term by term. The expected parity at the AND input is $2^{-|S|}$ (\texttt{expect\_parity\_signCubeAnd}); each of the two pairwise products with that parity has the same expectation, $2^{-|S|}$ (\texttt{expect\_parity\_mul\_parity\_signCubeAnd\_first} and \texttt{expect\_parity\_mul\_parity\_signCubeAnd\_second}); and the triple product has expectation $(-1/2)^{|S|}$ (\texttt{expect\_parity\_mul\_parity\_mul\_parity\_signCubeAnd}). Substitution gives $\frac12+3\cdot2^{-|S|}/4-(-1/2)^{|S|}/4$, which rewrites as the claimed expression.

**Key facts.** `FABL.signAndFunctionTester_acceptanceProbability`, `FABL.signAnd_indicator`, `FABL.expect_parity_signCubeAnd`, `FABL.expect_parity_mul_parity_signCubeAnd_first`, `FABL.expect_parity_mul_parity_signCubeAnd_second`, `FABL.expect_parity_mul_parity_mul_parity_signCubeAnd`.
