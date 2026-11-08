<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.stableInfluence_improvedFriedgutRho_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improved Stable Influence Bound

**Claim.** For positive $\eta,\tau$, if the Boolean influence of $f$ at $i$ is less than $\tau$, then its stable influence at $\eta/(2+\eta)$ is at most $\tau^{1/(1+\eta)}$ times its Boolean influence.

**Proof.** Put $\rho=\eta/(2+\eta)$ and $b=1/(1+\eta)$. The positivity and upper-bound facts for the improved parameter (`improvedFriedgutRho_pos`, `improvedFriedgutRho_le_one`) give $\rho\in[0,1]$, and $b>0$. Direct algebra gives $2/(1+\rho)=1+b$. The stable-influence estimate (`stableInfluence_le_booleanInfluence_rpow`) therefore bounds the stable influence by $I^{1+b}$, where $I$ is the Boolean influence at $i$. This influence is nonnegative because it equals the ordinary influence of the real-valued function (`booleanInfluence_eq_influence_toReal`, `influence_nonneg`). If $I=0$, the estimate gives zero and the desired bound follows. If $I>0$, rewrite $I^{1+b}=I\,I^b$. Since $I<\tau$ and $b>0$, monotonicity of positive real powers gives $I^b\leq\tau^b$. Multiplying by $I\geq0$ and rearranging the factors proves the result.

**Key facts.** `FABL.improvedFriedgutRho_pos`, `FABL.improvedFriedgutRho_le_one`, `FABL.booleanInfluence_eq_influence_toReal`, `FABL.influence_nonneg`, `FABL.stableInfluence_le_booleanInfluence_rpow`.
