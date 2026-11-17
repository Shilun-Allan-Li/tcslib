<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Randomization/Basic.lean :: BooleanAnalysis.Hypercontractivity.RandomizationAux.component_laplacian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Components of a coordinate Laplacian

**Claim.** The $S$-component of the difference between $f$ and its conditional expectation given all coordinates except $i$ is the $S$-component of $f$ if $i\in S$, and zero otherwise.

**Proof.** By linearity of the component operation, its value on the difference defining the coordinate Laplacian is the $S$-component of $f$ minus the $S$-component of its conditional expectation given all coordinates except $i$. The conditional-expectation component rule (`component_condExp`) identifies the second term as the original component if $S$ is contained in the coordinates other than $i$, and as zero otherwise. Since $S$ is always contained in the full coordinate set, it is contained in that set with $i$ removed exactly when $i\notin S$. Subtracting in these two cases gives the asserted formula.

**Key facts.** `BooleanAnalysis.Hypercontractivity.RandomizationAux.component_condExp`.
