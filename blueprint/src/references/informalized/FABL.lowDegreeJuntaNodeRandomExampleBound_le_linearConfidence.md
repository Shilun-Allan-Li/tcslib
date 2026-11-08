<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaNodeRandomExampleBound_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Random-Example Bound

**Claim.** The maximum over all subsets $P\subseteq[n]$ of the node’s random-example count at the specified dyadic node-failure parameter is bounded by the stated linear-confidence expression.

**Proof.** Unfold the maximum, which is the supremum over the finite family of subsets $P\subseteq[n]$. It suffices to prove the desired bound separately for each such $P$. The established fixed-$P$ estimate, `FABL.lowDegreeJuntaNodeRandomExamples_le_linearConfidence`, gives exactly that inequality with the same coefficient, resource exponent, and confidence factor. Taking the supremum preserves the common upper bound.

**Key facts.** `FABL.lowDegreeJuntaNodeRandomExamples_le_linearConfidence`.
