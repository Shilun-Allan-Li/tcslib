<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.splitLastTwoLinearEquiv_appendTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting Off Two Coordinates

**Claim.** Under the linear coordinate identification of $\mathbb{F}_2^{m+2}$ with $\mathbb{F}_2^m\times(\mathbb{F}_2\times\mathbb{F}_2)$, appending $a,b$ to $x$ maps to $(x,(a,b))$.

**Proof.** The coordinate identification first separates a vector of length $m+2$ into its first $m$ entries and its final two entries. Applied to the vector formed by appending $a,b$ to $x$, these parts are $x$ and the two-coordinate vector $(a,b)$. The second identification reads that final vector as the ordered pair $(a,b)$, giving $(x,(a,b))$.
