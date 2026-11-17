<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.learningConsequencesCoordinateRatio_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate ratio bound

**Claim.** Under the stated subsquare-root regime assumptions, the coordinate ratio $2t/\theta$ is bounded by the specified power of two.

**Proof.** Write $s=\sqrt{\lceil\log_2(n+1)\rceil}+1$, $A=8(C+1)(Q+1)+1$, $K_0=128(Q+1)^2(C+1)^3$, and $k=d$. The degree estimate (FABL.learningConsequencesDegree_le_subsqrt) gives $k\le As$, while the regime gives $t\le(C+1)s$. Also, the lower bound on $\varepsilon$ implies the internal error $\eta=\varepsilon/8$ is at least $1/(8(Q+1))$, and positivity of $t$ and $\eta$ permits the following comparisons. From the definition of $\theta$, the ratio equals $2t^3\eta^{-2}9^k$. Replacing $t$ by its upper bound, $\eta$ by its positive lower bound, and $k$ by $As$ bounds this by $K_0s^3 9^{As}$. Now $K_0\le2^{K_0s}$ by the elementary estimate $m\le2^m$, and $s^3\le2^{3s}$ by applying the same estimate to $s$. Finally, $9^{As}\le16^{As}=2^{4As}$. Multiplying these estimates yields $K_0s^3 9^{As}\le2^{(K_0+4A+3)s}$, which is the asserted exponent.

**Key facts.** `FABL.learningConsequencesDegree_le_subsqrt`, `FABL.learningConsequencesInternalError_pos`, `FABL.nat_self_le_two_pow`.
