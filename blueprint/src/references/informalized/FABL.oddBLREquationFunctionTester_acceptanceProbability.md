<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.oddBLREquationFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tester Acceptance as a Uniform Average

**Claim.** For every Boolean function, the tester’s acceptance probability equals the uniform average over independent uniform $x,y$ and uniform sign $b$ of the indicator that $f(x)f(y)f(bxy)=b$.

**Proof.** The tester samples a seed consisting of a pair of sign-cube points $x,y$ and a sign $b$. Its three queries are exactly $x$, $y$, and the point whose $i$th coordinate is $b x_i y_i$, and its acceptance rule checks whether the product of the three answers equals $b$. By the uniform-PMF expectation identity (`pmfExpectation_uniformPMF_eq_expect`), its acceptance probability is the uniform average of this indicator over the seed space. The seed space is a product of the two cubes and the sign set; factoring the uniform average over these finite products gives the stated iterated expectation. The transcript evaluation identity (`NonadaptiveFunctionTester.transcript_apply`) identifies each answer with the value of $f$ at its corresponding query, and the definition of the acceptance predicate turns the test into precisely the displayed equality indicator.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.NonadaptiveFunctionTester.transcript_apply`.
