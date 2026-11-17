<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.injectionVectorSplitEquiv_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Along an Injection

**Claim.** Under the canonical decomposition of assignments on the larger index set into values on the image of the injection and its complement, the first component at $i$ is $x(e(i))$.

**Proof.** The decomposition first restricts the assignment $x$ to the image of the injection. Its first component is then reindexed from that image by the inverse of the injection regarded as a bijection onto its range. Evaluating at $i$ therefore reads the restricted assignment at the image point corresponding to $i$, namely $x(e(i))$.
