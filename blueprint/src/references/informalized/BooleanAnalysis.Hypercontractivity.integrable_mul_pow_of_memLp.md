<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.integrable_mul_pow_of_memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of Products of Powers

**Claim.** On a finite measure space, if $f$ and $g$ belong to $L^p$ and $a+b\leq p$ for natural numbers $a,b$, then $f^a g^b$ is integrable.

**Proof.** If $p=0$, the inequality forces $a=b=0$, so the product is the constant function $1$, which is integrable under a finite measure. Otherwise, the constant function $1$ and the norms of $f$ and $g$ all belong to $L^p$. Their sum $z=1+|f|+|g|$ therefore belongs to $L^p$. Pointwise, $z\geq1$, $|f|\leq z$, and $|g|\leq z$, so $|f^a g^b|\leq z^{a+b}\leq z^p$. Thus the product is dominated by an integrable $p$th-power bound; its measurability follows from the $L^p$ strong measurability of $f$ and $g$. The domination criterion for integrability gives the result.
