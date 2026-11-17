<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.subsetLocalCorrectionFunctionTester_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability on a Dictator

**Claim.** For the subset local correction tester and the dictator indexed by $i$, the acceptance probability is $1$ if $i$ belongs to $S$, and $0$ otherwise.

**Proof.** The tester samples a uniform binary vector $y$, queries the dictator at the sign encodings of $y$ and $x+y$, and accepts exactly when the product of the answers is $-1$. The uniform-PMF expectation identity (`pmfExpectation_uniformPMF_eq_expect`) therefore expresses acceptance as the uniform expectation of the indicator of this product condition. At coordinate $i$, the two answers are the sign encodings of $y_i$ and $x_i+y_i$. Since encoding addition multiplies signs (`signEncode_add`), and each sign squares to $1$, their product reduces to the sign encoding of $x_i$. The binary-to-sign equivalence identifies that sign with the subset indicator at $i$ (`binaryCubeSignEquiv_apply` and the equivalence’s inverse law). The product is consequently $-1$ exactly when $i\in S$. The integrand is constant in $y$, so its uniform expectation is $1$ in that case and $0$ otherwise.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.binaryCubeSignEquiv_apply`, `FABL.signEncode_add`.
