<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.blrAndNae_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combined BLR and NAE local tester

**Claim.** The combined BLR and NAE tests form a 6-query local tester for dictators with rejection rate $0.1$.

**Proof.** The proof first reduces the local-tester claim to completeness and a closeness implication using `FABL.isLocalTester_of_close_of_acceptanceProbability_ge`. The rate is positive. For completeness, a dictator is accepted by the BLR test with probability one (`FABL.signBlrFunctionTester_complete`) and by the NAE test with probability one (`FABL.naeFunctionTester_complete_signedDictator`); the combined tester's acceptance probability is their product (`FABL.andFunctionTester_acceptanceProbability`), hence is also one. For soundness, if the combined acceptance probability is at least $1-0.1\varepsilon$, the product formula and the fact that each individual acceptance probability lies between zero and one (`FABL.NonadaptiveFunctionTester.acceptanceProbability_le_one`, `FABL.NonadaptiveFunctionTester.acceptanceProbability_nonneg`) imply that each individual probability is at least $1-0.1\varepsilon$. The joint BLR-and-NAE closeness result (`FABL.exists_dictator_close_of_signBlr_and_nae_acceptance_ge`) then supplies a dictator within distance $\varepsilon$. Applying the reduction yields the claimed tester property.

**Key facts.** `FABL.isLocalTester_of_close_of_acceptanceProbability_ge`, `FABL.signBlrFunctionTester_complete`, `FABL.naeFunctionTester_complete_signedDictator`, `FABL.andFunctionTester_acceptanceProbability`, `FABL.NonadaptiveFunctionTester.acceptanceProbability_le_one`, `FABL.NonadaptiveFunctionTester.acceptanceProbability_nonneg`, `FABL.exists_dictator_close_of_signBlr_and_nae_acceptance_ge`.
