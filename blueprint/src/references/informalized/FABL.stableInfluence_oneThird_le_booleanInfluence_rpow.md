<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.stableInfluence_oneThird_le_booleanInfluence_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Third Stable Influence Power Bound

**Claim.** For Boolean $f$ and any coordinate $i$, the stable influence at parameter $1/3$ is at most the Boolean influence of coordinate $i$ raised to the power $3/2$.

**Proof.** First use the preceding bound (\texttt{stableInfluence_oneThird_le_booleanInfluence_mul_sqrt}) to bound the stable influence by $a\sqrt a$, where $a$ is the Boolean influence. If $a=0$, this bound gives zero on the right, and the desired power expression is also zero. If $a\ne0$, nonnegativity of ordinary influence, together with its equality to Boolean influence (\texttt{booleanInfluence_eq_influence_toReal} and \texttt{influence_nonneg}), shows $a>0$. For positive $a$, the identity $a^{3/2}=a\sqrt a$ (\texttt{rpow_three_halves_eq_mul_sqrt}) converts the preceding bound into the claimed one.

**Key facts.** `FABL.stableInfluence_oneThird_le_booleanInfluence_mul_sqrt`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`, `FABL.rpow_three_halves_eq_mul_sqrt`.
