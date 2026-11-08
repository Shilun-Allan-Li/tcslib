<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.matches_insertJuntaFixedAssignment_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching an Extended Fixed Assignment

**Claim.** An input matches the fixed assignment extended by setting coordinate $i$ to $v$ exactly when it matches the original assignment on $P$ and has value $v$ at coordinate $i$.

**Proof.** If the input matches the extended assignment, then restricting that agreement to coordinates already in $P$ gives agreement with the original assignment; agreement at the newly inserted coordinate gives $x_i=v$. Conversely, suppose both agreements hold. Any coordinate in the enlarged set either is the newly inserted coordinate, where the desired equality is the assumed value at $i$, or was already in $P$, where it follows from the original matching condition. These cases establish agreement everywhere in the enlarged set.
