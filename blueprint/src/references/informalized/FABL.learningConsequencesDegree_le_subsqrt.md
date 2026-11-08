<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.learningConsequencesDegree_le_subsqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound in the subsquare-root regime

**Claim.** Under the stated regime hypotheses, the degree $d=\lceil 8t/\varepsilon\rceil$ is bounded by $[8(C+1)(Q+1)+1](\sqrt{\lceil\log_2(n+1)\rceil}+1)$.

**Proof.** Put $s=\sqrt{\lceil\log_2(n+1)\rceil}+1$ and $A=8(C+1)(Q+1)+1$. The precision hypothesis implies $1\le(Q+1)\varepsilon$. The influence hypothesis gives $t\le(C+1)s$. Multiplying the latter by $8$, then using the precision inequality, gives $8t\le8(C+1)s\le8(C+1)(Q+1)s\varepsilon\le A s\varepsilon$. Since $\varepsilon>0$, division by $\varepsilon$ yields $8t/\varepsilon\le As$. The ceiling bound for a nonnegative rational then gives $d=\lceil8t/\varepsilon\rceil\le As$.
