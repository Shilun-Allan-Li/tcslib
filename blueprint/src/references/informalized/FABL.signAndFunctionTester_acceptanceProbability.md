<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.signAndFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability of the Sign-AND Tester

**Claim.** The tester’s acceptance probability equals the uniform expectation over independent sign cubes $x,y$ of the indicator that $f(x)\wedge f(y)=f(x\wedge y)$.

**Proof.** The tester’s seed consists of a pair $(x,y)$ of sign cubes, sampled uniformly, and its three queries return $f(x)$, $f(y)$, and $f(x\wedge y)$. The transcript records each query answer by applying the function to its query address (\texttt{NonadaptiveFunctionTester.transcript\_apply}). Consequently, the tester accepts exactly when the stated sign-AND equality holds. The expectation of the acceptance indicator under the uniform seed distribution is the uniform expectation over seed pairs (\texttt{pmfExpectation\_uniformPMF\_eq\_expect}); factoring the uniform expectation over the product seed space yields the iterated expectation over $x$ and $y$.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
