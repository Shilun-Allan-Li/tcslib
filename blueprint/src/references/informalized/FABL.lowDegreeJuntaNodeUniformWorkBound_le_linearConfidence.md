<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaNodeUniformWorkBound_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Node Work Bound

**Claim.** For all $n,k,b$, the maximum of the node work bounds over subsets $P\subseteq[n]$, at the specified dyadic node failure parameter, satisfies the stated linear-confidence estimate.

**Proof.** The node work estimate applies to each subset $P$ individually, with the same right-hand side depending only on $n,k,b$. Therefore that right-hand side is an upper bound for every value in the finite supremum defining the uniform node work bound, and hence bounds the supremum itself.

**Key facts.** `FABL.lowDegreeJuntaNodeWorkBound_le_linearConfidence`.
