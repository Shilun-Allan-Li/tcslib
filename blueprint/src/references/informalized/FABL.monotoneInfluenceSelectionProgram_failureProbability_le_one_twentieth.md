<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequences.lean :: FABL.monotoneInfluenceSelectionProgram_failureProbability_le_one_twentieth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence-Selection Failure Bound

**Claim.** The displayed exercise asks for query and random-example learnability results for Boolean functions with small influence, including the decision-tree-size consequence.

**Proof.** The proof establishes a more specific claim: the event that the selected coordinate set fails to contain all coordinates above the influence threshold, or exceeds the coordinate cap, has probability at most $1/20$. Let $\mathcal F$ be the singleton Fourier family, and let the failure event be viewed as a set of sample-input matrices. If a matrix lies outside every bad coefficient-estimation set, the no-bad-estimates lemma says the true influential coordinates are contained in the empirically selected set (`influentialCoordinates_subset_empiricalInfluentialCoordinates_of_no_bad`). The empirical set also has cardinality at most the coordinate cap (`card_empiricalInfluentialCoordinates_le`). Together these contradict either part of the failure condition, so the failure event is contained in the union of the bad estimation sets. The program's event probability is the measure of the preimage of this event under the matrix-output map (`randomExampleMatrixOutputLaw_toOuterMeasure_apply`). By monotonicity of measure, it is at most the measure of that union; the finite-family coefficient-estimation bound makes this at most $|\mathcal F|$ times the confidence parameter (`measure_finiteFamily_someCoefficientBadSetWithParameters_le`). Finally $|\mathcal F|=n$ (`card_singletonFourierFamily`), and the chosen confidence is $1/(20(n+1))$, so $n/(20(n+1))\le 1/20$.

**Key facts.** `FABL.influentialCoordinates_subset_empiricalInfluentialCoordinates_of_no_bad`, `FABL.card_empiricalInfluentialCoordinates_le`, `FABL.randomExampleMatrixOutputLaw_toOuterMeasure_apply`, `FABL.measure_finiteFamily_someCoefficientBadSetWithParameters_le`, `FABL.card_singletonFourierFamily`.

**Caveat.** The supplied informal statement is an exercise about learnability, while the formal statement and proof establish only the influence-selection failure bound described above.
