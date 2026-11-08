<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.map_uniformPMF_fst -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Marginal of a Uniform Distribution

**Claim.** For finite nonempty sets $A$ and $B$, projecting a uniformly chosen element of $A\times B$ onto $A$ gives the uniform distribution on $A$.

**Proof.** Fix $a\in A$. There are exactly $|B|$ pairs in $A\times B$ whose first coordinate is $a$, and each pair has uniform mass $1/(|A||B|)$. Summing these masses gives $|B|/(|A||B|)=1/|A|$, which is the uniform mass of $a$.
