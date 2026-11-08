<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.boolAndFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability of the Boolean AND tester

**Claim.** The Boolean AND tester's acceptance probability equals the uniform expectation over independent uniform inputs $x,y$ of the indicator that $f(x)\wedge f(y)=f(x\wedge y)$.

**Proof.** The tester's seed is the pair $(x,y)$, and its distribution is uniform. Its three queries return $f(x)$, $f(y)$, and $f(x\wedge y)$, so its acceptance indicator is precisely the indicator of the displayed equality. Converting the expectation under the uniform seed distribution to uniform expectation gives an expectation over pairs $(x,y)$. The uniform expectation on a product of finite spaces factors as iterated uniform expectation, yielding the asserted expression.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.NonadaptiveFunctionTester.transcript_apply`.
