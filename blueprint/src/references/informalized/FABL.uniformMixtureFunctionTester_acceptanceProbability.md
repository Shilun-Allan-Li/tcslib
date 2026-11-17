<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.uniformMixtureFunctionTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance probability of a tester mixture

**Claim.** The acceptance probability of a tester formed by choosing uniformly among $T_1,\ldots,T_t$ and then sampling that tester's seed is the uniform average of their individual acceptance probabilities on $f$.

**Proof.** The mixture first samples an index uniformly from $\{1,\ldots,t\}$, then samples a seed from the selected tester's distribution, and accepts according to that tester's predicate on the resulting transcript. The expectation of an acceptance indicator under a two-stage probability law is the outer expectation of its conditional expectation (\texttt{pmfExpectation\_bind}). Mapping a seed to the tagged seed that records its tester preserves this expectation as the expectation of the composed indicator (\texttt{pmfExpectation\_map}). Thus, for each fixed index, the inner expectation is precisely that tester's acceptance probability. Finally, expectation under the uniform law on indices is the uniform finite expectation (\texttt{pmfExpectation\_uniformPMF\_eq\_expect}), giving the asserted average.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_map`, `FABL.pmfExpectation_uniformPMF_eq_expect`.
