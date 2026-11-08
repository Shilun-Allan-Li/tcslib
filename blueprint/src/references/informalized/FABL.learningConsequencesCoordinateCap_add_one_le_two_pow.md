<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.learningConsequencesCoordinateCap_add_one_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate cap bound

**Claim.** Under the subsquare-root regime hypotheses, the coordinate cap increased by one is bounded by the stated power of two.

**Proof.** Set $s=\sqrt{\lceil\log_2(n+1)\rceil}+1$, let $A=8(C+1)(Q+1)+1$, and let $K_0=128(Q+1)^2(C+1)^3$. The coordinate ratio estimate (FABL.learningConsequencesCoordinateRatio_le_two_pow) bounds $2t/\theta$ by $2^e$, where $e=(K_0+4A+3)s$. Since the coordinate cap is the ceiling of that ratio, it is at most $2^e$. The exponents satisfy $e+1\le Bs$, where $B=K_0+4A+5$; this uses $s\ge1$ and direct expansion. Hence the cap plus one is at most $2^e+1\le 2^e+2^e=2^{e+1}\le2^{Bs}$, which is the claimed bound.

**Key facts.** `FABL.learningConsequencesCoordinateRatio_le_two_pow`.
