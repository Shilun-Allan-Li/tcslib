<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.norm_le_of_pairing -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted norm bound from pairings

**Claim.** If every pairing of $z$ with a function $g$ is bounded by $N$ times the weighted conjugate-exponent norm of $g$, then the weighted $q$-norm of $z$ is at most $N$.

**Proof.** Set $r=q/(q-1)$ and choose the dual function $g_i=z_i|z_i|^{q-2}$. The signed-power duality identity (`BooleanAnalysis.Hypercontractivity.FiniteNorms.signed_power_dual`) gives both $z_i g_i=|z_i|^q$ and $|g_i|^r=|z_i|^q$. Write $M=\sum_i w_i|z_i|^q$, which is nonnegative because the weights are nonnegative. The assumed pairing bound applied to this $g$ therefore gives $M\le N M^{1/r}$. If $M=0$, the desired norm is zero and the result follows from $N\ge0$. If $M>0$, divide by the positive quantity $M^{1/r}$. Since $1/q+1/r=1$, the resulting inequality is $M^{1/q}\le N$, as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteNorms.signed_power_dual`.
