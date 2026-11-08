<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.prefixLastTwoLinearMap_appendTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection after appending two coordinates

**Claim.** For a vector $x\in\mathbb{F}_2^m$ and coordinates $a,b\in\mathbb{F}_2$, projecting the vector obtained by appending $a,b$ onto its first $m$ coordinates returns $x$.

**Proof.** Unfold the projection: the linear equivalence first splits the appended vector into its initial block and its final pair, and the projection then takes the first component. Splitting the vector formed by appending $a,b$ recovers the pair $(x,(a,b))$, so its first component is $x$.
