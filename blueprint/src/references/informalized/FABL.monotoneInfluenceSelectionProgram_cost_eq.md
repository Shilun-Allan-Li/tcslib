<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.monotoneInfluenceSelectionProgram_cost_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence-Selection Program Cost

**Claim.** Every supported outcome of the influence-selection program has cost exactly $(nm,0,nm+nm(n+1)+n)$, where $m$ is its singleton-influence sample count.

**Proof.** The program draws one sample batch for each member of the singleton Fourier family and then charges its specified local work. Unwinding the output law, any outcome in its support comes from some choice of sample inputs; the output may depend on those inputs, but its cost is fixed by the matrix-outcome rule: $(|\mathcal F|m,0,|\mathcal F|m+|\mathcal F|m(n+1)+n)$. The singleton Fourier family has cardinality $n$ (`card_singletonFourierFamily`). Substituting this and simplifying the natural-number expression gives the stated cost.

**Key facts.** `FABL.card_singletonFourierFamily`.
