<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.stableInfluence_one_third_le_sqrt_max_mul_influence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Versus Maximum Influence

**Claim.** For every Boolean $f$ and coordinate $i$, the stable influence at parameter $1/3$ is at most $\sqrt{\operatorname{MaxInf}[f]}\,\operatorname{Inf}_i[f]$.

**Proof.** Both the stable influence and the ordinary influence are nonnegative (\texttt{stableInfluence_nonneg} and \texttt{influence_nonneg}), and the maximum influence is nonnegative (\texttt{maximumInfluence_nonneg}). Also, the influence of coordinate $i$ is bounded by the maximum influence, using the identification of Boolean and ordinary influence (\texttt{booleanInfluence_eq_influence_toReal}) and the coordinatewise maximum bound (\texttt{booleanInfluence_le_maximumInfluence}). It is therefore enough to compare squares. The squared stable-influence estimate (\texttt{stableInfluence_one_third_sq_le_booleanInfluence_cube}) bounds the square by the cube of the coordinate influence. The cube is at most the maximum influence times the square of that coordinate influence, since the coordinate influence is nonnegative and at most its maximum. Finally, this product is the square of $\sqrt{\operatorname{MaxInf}[f]}\,\operatorname{Inf}_i[f]$. Taking square roots, or equivalently comparing the nonnegative quantities by their squares, gives the result.

**Key facts.** `FABL.stableInfluence_nonneg`, `FABL.influence_nonneg`, `FABL.maximumInfluence_nonneg`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.booleanInfluence_le_maximumInfluence`, `FABL.stableInfluence_one_third_sq_le_booleanInfluence_cube`.
