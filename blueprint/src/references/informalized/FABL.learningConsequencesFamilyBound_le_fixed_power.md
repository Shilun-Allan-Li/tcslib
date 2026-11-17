<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.learningConsequencesFamilyBound_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-power family-size bound

**Claim.** Under the subsquare-root regime hypotheses, the family size is at most $2^{2e}(n+1)^e$ for the specified exponent $e$.

**Proof.** Let $L=\lceil\log_2(n+1)\rceil$, $s=\sqrt L+1$, $A=8(C+1)(Q+1)+1$, $B=128(Q+1)^2(C+1)^3+4A+5$, $E=2A(B+1)$, and $k=d$. The degree estimate (FABL.learningConsequencesDegree_le_subsqrt) gives $k\le As$, and the coordinate cap estimate (FABL.learningConsequencesCoordinateCap_add_one_le_two_pow) gives $k_{\mathrm{cap}}+1\le2^{Bs}$. Also, $k+1\le2^{As}$, since $k\le As$ and $m+1\le2^m$ (FABL.nat_succ_le_two_pow). Therefore the family bound $(k+1)(k_{\mathrm{cap}}+1)^k$ is at most $2^{As}(2^{Bs})^{As}=2^{As+ABs^2}$. The square-root estimate $(\sqrt L+1)^2\le2(L+1)$ (FABL.sqrt_add_one_sq_le_two_mul_add_one), together with $s\ge1$, shows $As+ABs^2\le A(B+1)s^2\le E(L+1)$. Hence the family bound is at most $2^{E(L+1)}$. Finally, $2^L\le2(n+1)$ (FABL.two_pow_clog_le_two_mul) gives $2^{E(L+1)}=2^E(2^L)^E\le2^E(2(n+1))^E=2^{2E}(n+1)^E$, proving the result.

**Key facts.** `FABL.learningConsequencesDegree_le_subsqrt`, `FABL.learningConsequencesCoordinateCap_add_one_le_two_pow`, `FABL.nat_succ_le_two_pow`, `FABL.sqrt_add_one_sq_le_two_mul_add_one`, `FABL.two_pow_clog_le_two_mul`.
