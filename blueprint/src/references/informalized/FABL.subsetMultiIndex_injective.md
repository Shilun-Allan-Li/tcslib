<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedAnalysis.lean :: FABL.subsetMultiIndex_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of Subset Indices

**Claim.** The map sending a finite subset $S$ to its index, equal to $1$ on $S$ and $0$ elsewhere, is injective.

**Proof.** Suppose two subsets have the same index. At each coordinate their index values agree. If the coordinate belongs to the first subset, its index value is $1$, forcing it to belong to the second; conversely, membership in the second forces membership in the first. Thus the subsets have the same elements and are equal.
