<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.zeropVerifier_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Polynomial Verifier Specification

**Claim.** For a finite Boolean string $x$, the verifier accepts with probability at least $2/3$ on a uniformly random string of length $2400(|x|+1)^2$ when $x$ is not an encoding of a well-formed integer arithmetic circuit with identically zero output polynomial. When $x$ is such an encoding, the verifier rejects for every random string of that length.

**Proof.** Prove the two implications separately. First suppose $x\notin\mathrm{ZEROP}$ and consider whether decoding succeeds. If decoding fails, the verifier accepts on every random string, so its acceptance probability is $1$ (`Randomized.randProb_congr`, `Randomized.randProb_true`). If decoding yields a circuit $C$ that is not well formed, the verifier again accepts on every string, giving the same bound. If decoding yields a well-formed $C$, then its output polynomial is nonzero: otherwise the characterization of membership in $\mathrm{ZEROP}$ (`Randomized.mem_ZEROP_iff`) would imply $x\in\mathrm{ZEROP}$. The test uses no more random bits than the specified budget: the test-length bound applies to the decoded circuit, and the encoding agrees with $x$ whenever decoding succeeds (`Randomized.testLen_le_polyLen`, `Randomized.AlgCircuit.encode_of_decode`). The soundness theorem for the zero test therefore gives probability at least $2/3$ that the test rejects, which is exactly when the verifier accepts in this case (`Randomized.randProb_congr`, `Randomized.AlgCircuit.zeroTest_sound`).

For the other implication, suppose $x\in\mathrm{ZEROP}$. The membership characterization supplies a decoded, well-formed circuit $C$ whose output polynomial is zero (`Randomized.mem_ZEROP_iff`). On every random string, the zero-polynomial test returns true (`Randomized.AlgCircuit.zeroTest_of_toMvPolynomial_eq_zero`). The verifier negates that test for a well-formed decoded circuit, so it rejects on every such string, as claimed.

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_true`, `Randomized.mem_ZEROP_iff`, `Randomized.testLen_le_polyLen`, `Randomized.AlgCircuit.encode_of_decode`, `Randomized.randProb_congr`, `Randomized.AlgCircuit.zeroTest_sound`, `Randomized.mem_ZEROP_iff`, `Randomized.AlgCircuit.zeroTest_of_toMvPolynomial_eq_zero`.
