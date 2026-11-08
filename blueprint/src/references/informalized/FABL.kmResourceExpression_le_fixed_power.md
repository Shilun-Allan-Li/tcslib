<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.kmResourceExpression_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resource expression power bound

**Claim.** Under the given bounds on $M+1$ and $(1/\varepsilon)^{10}$, the resource expression is at most $L(F+1)^8Q^{10}(n+1)^{8E+d}$.

**Proof.** Raise $M+1\le (F+1)(n+1)^E$ to the eighth power. Since all quantities are nonnegative, this gives $(M+1)^8\le (F+1)^8(n+1)^{8E}$. Regard this inequality in the rationals and multiply it by the nonnegative factor $L(n+1)^d(1/\varepsilon)^{10}$. The original expression has the same value as this product, since $\varepsilon>0$ and hence $1/\varepsilon^{10}=(1/\varepsilon)^{10}$. Next apply the assumed bound $(1/\varepsilon)^{10}\le Q^{10}$, multiplying by the other nonnegative factors. The resulting expression is $L(F+1)^8Q^{10}(n+1)^{d+8E}$; combining powers gives the stated exponent $8E+d$.
