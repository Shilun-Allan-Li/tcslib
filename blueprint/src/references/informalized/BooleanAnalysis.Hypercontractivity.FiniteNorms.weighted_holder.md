<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Norms.lean :: BooleanAnalysis.Hypercontractivity.FiniteNorms.weighted_holder -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weighted Hölder inequality

**Claim.** For a finite set with nonnegative weights and Hölder-conjugate exponents $p,q$, the weighted sum of products is bounded above by the product of the corresponding weighted $p$- and $q$-norms.

**Proof.** First, replace each product $f_i g_i$ by its absolute value; this can only increase the sum because each weight is nonnegative. Since $1/p+1/q=1$, the factors $w_i^{1/p}$ and $w_i^{1/q}$ multiply to $w_i$. Thus each resulting summand can be written as $(w_i^{1/p}|f_i|)(w_i^{1/q}|g_i|)$. Apply the finite-sum Hölder inequality to these two nonnegative families. Raising each factor inside the resulting sums to its conjugate exponent gives $w_i|f_i|^p$ and $w_i|g_i|^q$, respectively, which is the claimed bound.
