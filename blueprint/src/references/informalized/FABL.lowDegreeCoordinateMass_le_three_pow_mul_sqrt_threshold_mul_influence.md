<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.lowDegreeCoordinateMass_le_three_pow_mul_sqrt_threshold_mul_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Mass Influence Bound

**Claim.** For a sign-valued Boolean function $f$, threshold $\tau$, natural number $k$, and coordinate $i$ outside the influential coordinates at threshold $\tau$, the low-degree coordinate mass through degree $k$ is at most $3^k\sqrt{\tau}$ times the Boolean influence of $i$.

**Proof.** Because $i$ is outside the influential-coordinate set, its Boolean influence is less than $\tau$. The Boolean influence equals the influence of the real-valued version of $f$, and this influence is nonnegative. First bound the low-degree coordinate mass by $3^k$ times the stable influence at parameter $1/3$. The stable influence bound then gives at most $3^k$ times the Boolean influence multiplied by the square root of that influence. Since the influence is nonnegative and less than $\tau$, monotonicity of the square root gives $\sqrt{\operatorname{Inf}_i[f]}\le\sqrt{\tau}$. Multiplying by the nonnegative influence and by $3^k$ preserves the inequality; rearranging the final product yields the claimed bound.

**Key facts.** `FABL.not_mem_influentialCoordinates`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`, `FABL.lowDegreeCoordinateMass_le_three_pow_mul_stableInfluence`, `FABL.stableInfluence_oneThird_le_booleanInfluence_mul_sqrt`.

**Caveat.** The supplied informal statement describes a different influence-sum assertion; this account follows the formal statement and proof source, which establish the low-degree coordinate-mass bound.
