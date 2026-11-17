<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/Sequence.lean :: BooleanAnalysis.GaussianSpace.Invariance.independent_input_coupling -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Independent Coupling of Two Families

**Claim.** Two finite families of real random variables on possibly different probability spaces can be realized together as mutually independent coordinates, with each coordinate retaining the distribution of its corresponding original variable.

**Proof.** For each index in the disjoint union, take its prescribed law: the pushforward of $\mu$ under $X_i$ on the left, and the pushforward of $\nu$ under $Y_i$ on the right. Almost everywhere measurability ensures each pushforward is a probability measure. Form the finite product measure of all these laws on the space of coordinate vectors, and let each random variable be the corresponding coordinate projection. Product coordinates are mutually independent, and each projection has its designated marginal law. Thus the left and right coordinates have the required distributions.
