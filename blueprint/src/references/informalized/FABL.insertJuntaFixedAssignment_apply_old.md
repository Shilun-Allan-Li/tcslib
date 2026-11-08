<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.insertJuntaFixedAssignment_apply_old -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values on original coordinates

**Claim.** At every coordinate in the original set $P$, the extended assignment agrees with the original assignment $z$.

**Proof.** Fix $j\in P$. Since $i\notin P$, the coordinate $j$ cannot equal $i$. Thus the extension uses its old-assignment case at $j$, and the old value read there is $z(j)$.
