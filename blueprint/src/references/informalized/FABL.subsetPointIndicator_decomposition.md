<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.subsetPointIndicator_decomposition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition by Point Indicators

**Claim.** Every real-valued function on the finite subsets is the sum, over all subsets $A$, of its value at $A$ times the point indicator of $A$.

**Proof.** Evaluate the proposed sum at an arbitrary subset $S$. The point indicator of $A$ at $S$ is zero unless $A=S$, and is one when $A=S$. Thus every summand vanishes except the term indexed by $S$, which equals the function’s value at $S$. The resulting functions agree at every subset.
