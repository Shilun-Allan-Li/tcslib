<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.totalInfluence_eq_sum_card_components -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Influence Decomposition

**Claim.** The total influence is the sum over all coordinate sets $S$ of $|S|$ times the expected squared $S$-component.

**Proof.** Expand each coordinate influence using the influence decomposition (`influence_eq_sum_components`) and interchange the two finite sums. For a fixed set $S$, its expected squared component then appears once for each coordinate in $S$ and not at all for coordinates outside $S$. Its total coefficient is therefore the number of elements of $S$, namely $|S|$, which gives the stated identity.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.influence_eq_sum_components`.
