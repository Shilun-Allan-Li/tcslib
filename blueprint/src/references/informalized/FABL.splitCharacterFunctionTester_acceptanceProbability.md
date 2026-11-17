<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.splitCharacterFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability of the split character tester

**Claim.** The tester’s acceptance probability is $(1+C)/2$, where $C$ is the expected product of the three queried sign values over independent uniform $a,b,h$.

**Proof.** Under the uniform seed distribution, a seed consists of independent uniform choices of $a,b,h$. The tester's three queries return the values at $(h,a)$, $(0,b)$, and $(0,a+b)$; unfolding the transcript records precisely these answers (`NonadaptiveFunctionTester.transcript_apply`). For signs $u,v,w$, the indicator that $uv=w$ is $(1+\operatorname{signValue}(u)\operatorname{signValue}(v)\operatorname{signValue}(w))/2$ (`splitCharacter_indicator_eq`). Thus the acceptance probability is the uniform expectation of one half times one plus the product of the three real sign values. Averaging separates the constant and the correlation: the uniform PMF expectation is the ordinary finite uniform expectation (`pmfExpectation_uniformPMF_eq_expect`), and expectation preserves this affine expression (`expect_one_add_div_two`). The remaining expected product is exactly $C$.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.splitCharacter_indicator_eq`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.expect_one_add_div_two`.
