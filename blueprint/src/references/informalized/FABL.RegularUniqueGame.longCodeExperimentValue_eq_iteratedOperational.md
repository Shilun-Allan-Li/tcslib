<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.longCodeExperimentValue_eq_iteratedOperational -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated experiment value

**Claim.** The long-code experiment value equals the average over uniform vertices of the seed-law average of the operational check value at each vertex.

**Proof.** Expand the experiment value as the expectation under its sampling law. The law first draws a uniform vertex, then a tester seed, and then the independent tuple of neighbours. The expectation-of-a-bind identity (\texttt{FABL.pmfExpectation\_bind}) converts these successive draws into nested expectations, and expectation under the uniform vertex law is the uniform finite average (\texttt{FABL.pmfExpectation\_uniformPMF\_eq\_expect}). For each fixed vertex, expand the seed and neighbour draws in the same way. The neighbour tuple is mapped into the experiment sample; the expectation-of-a-map identity (\texttt{FABL.pmfExpectation\_map}) identifies its payoff with the operational check payoff for that vertex and seed. This gives the asserted iterated average.

**Key facts.** `FABL.pmfExpectation_bind`, `FABL.pmfExpectation_uniformPMF_eq_expect`, `FABL.pmfExpectation_map`.
