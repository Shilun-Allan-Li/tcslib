<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/SmallSetExpansion.lean :: FABL.stableInfluence_oneThird_le_booleanInfluence_mul_sqrt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Third Stable Influence Bound

**Claim.** For Boolean $f$ and any coordinate $i$, the stable influence at parameter $1/3$ is at most $\operatorname{Inf}_i[f]^{3/2}$.

**Proof.** Write $A$ for the stable influence at $1/3$ and $a$ for the ordinary influence of coordinate $i$. The Boolean influence agrees with the ordinary influence of the real-valued function associated to $f$ (\texttt{booleanInfluence_eq_influence_toReal}), and ordinary influence is nonnegative (\texttt{influence_nonneg}); also $A\ge0$ by nonnegativity of stable influence (\texttt{stableInfluence_nonneg}). The squared bound (\texttt{stableInfluence_one_third_sq_le_booleanInfluence_cube}) gives $A^2\le a^3$. Since $a\ge0$, the right side of the desired inequality, $a\sqrt a$, is nonnegative and has square $a^3$. Comparing squares of these nonnegative quantities yields $A\le a\sqrt a$, as claimed.

**Key facts.** `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`, `FABL.stableInfluence_nonneg`, `FABL.stableInfluence_one_third_sq_le_booleanInfluence_cube`.
