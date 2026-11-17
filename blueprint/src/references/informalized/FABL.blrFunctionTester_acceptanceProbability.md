<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.blrFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tester Acceptance Probability

**Claim.** The acceptance probability of the BLR function tester equals the probability that uniformly sampled $x,y$ satisfy $f(x)+f(y)=f(x+y)$.

**Proof.** A seed of the tester is a pair $(x,y)$, chosen uniformly from the product of two copies of the cube. The tester queries $f(x)$, $f(y)$, and $f(x+y)$, and its transcript records those three answers in order. By the transcript formula (`NonadaptiveFunctionTester.transcript_apply`), the acceptance predicate on this transcript is precisely the equality $f(x)+f(y)=f(x+y)$. The uniform-seed expectation is the ordinary uniform expectation (`pmfExpectation_uniformPMF_eq_expect`). Since the seed space is a product, its expectation is the iterated expectation over independent uniform $x$ and $y$. Thus the tester's acceptance probability is exactly the probability of the stated BLR condition.

**Key facts.** `FABL.NonadaptiveFunctionTester.transcript_apply`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
