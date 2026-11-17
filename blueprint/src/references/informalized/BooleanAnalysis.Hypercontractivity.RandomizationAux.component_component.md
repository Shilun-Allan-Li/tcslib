<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.component_component -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of product components

**Claim.** Applying the $S$-component operation to the $T$-component of a function returns the original $S$-component when $S=T$, and returns zero otherwise.

**Proof.** Expand the outer component as an alternating sum of conditional expectations. The conditional expectation of a component given coordinates in $U$ is that component when its coordinate set is contained in $U$, and is zero otherwise (`condExp_component`). If $S=T$, only the term indexed by $S$ survives, giving the $S$-component of $f$. If $S\ne T$ and $S\subseteq T$, no subset $U\subseteq S$ can contain $T$, so every term vanishes. In the remaining case $S\not\subseteq T$, the surviving terms are governed by intersections with $T$; the alternating sum over subsets of $S$ of the resulting intersection-dependent values cancels to zero (`signed_intersection_zero`). This proves both cases.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.condExp_component`, `BooleanAnalysis.Hypercontractivity.RandomizationAux.signed_intersection_zero`.
