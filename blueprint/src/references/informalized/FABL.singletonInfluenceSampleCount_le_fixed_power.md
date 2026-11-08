<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.singletonInfluenceSampleCount_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Sample-Count Bound

**Claim.** Under the stated hypotheses, the sample count is at most $2560\cdot 2^{2E}(n+1)^{E+1}$.

**Proof.** Write $H=E$ and $s=\sqrt{\operatorname{clog}_2(n+1)}+1$. The subsquare-root sample-count bound gives a rational upper bound of $2560(n+1)2^{Hs}$. The elementary estimate $2^{H(\sqrt{\operatorname{clog}_2(n+1)}+1)}\le 2^{2H}(n+1)^H$ (`two_pow_mul_sqrt_clog_add_one_le_fixed_power`) replaces this factor by a fixed power of $n+1$, with constant factor $2^{2H}$. Substituting, and using $2560\cdot 2^{2H}(n+1)^{H+1}$ as the natural-number expression for the stated constant and exponent, gives the rational bound. Since the sample count and its proposed upper bound are natural numbers, the rational inequality yields the claimed natural-number inequality.

**Key facts.** `FABL.singletonInfluenceSampleCount_cast_le_subsqrt`, `FABL.two_pow_mul_sqrt_clog_add_one_le_fixed_power`.
