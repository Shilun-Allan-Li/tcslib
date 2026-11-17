<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.blrNae_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BLR and NAE Test Dictatorship

**Claim.** The BLR+NAE test is a $3$-query local tester for dictators with rejection rate $1/20$.

**Proof.** Use the local-tester criterion based on completeness and a closeness guarantee from high acceptance (`isLocalTester_of_close_of_acceptanceProbability_ge`). The rate $1/20$ is positive. For completeness, a dictator is accepted by both branches: the signed BLR branch by `signBlrFunctionTester_complete`, and the NAE branch by `naeFunctionTester_complete_signedDictator` with no negation. The uniform mixture's acceptance probability is the average of the two branch probabilities (`uniformMixtureFunctionTester_acceptanceProbability`), hence is one. For soundness, assume the mixture accepts with probability at least $1-(1/20)\varepsilon$. The component bound for a uniform mixture (`component_acceptanceProbability_ge_of_uniformMixture_ge`) implies that each branch accepts with probability at least $1-(1/10)\varepsilon$. The joint BLR and NAE closeness result (`exists_dictator_close_of_signBlr_and_nae_acceptance_ge`) then provides a dictator at relative Hamming distance at most $\varepsilon$. This establishes the closeness hypothesis of the criterion and proves the claimed rate.

**Key facts.** `FABL.isLocalTester_of_close_of_acceptanceProbability_ge`, `FABL.signBlrFunctionTester_complete`, `FABL.naeFunctionTester_complete_signedDictator`, `FABL.uniformMixtureFunctionTester_acceptanceProbability`, `FABL.component_acceptanceProbability_ge_of_uniformMixture_ge`, `FABL.exists_dictator_close_of_signBlr_and_nae_acceptance_ge`.
