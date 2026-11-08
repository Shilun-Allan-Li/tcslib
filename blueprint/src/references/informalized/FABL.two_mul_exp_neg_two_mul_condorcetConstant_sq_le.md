<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.two_mul_exp_neg_two_mul_condorcetConstant_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound for the Condorcet Constant

**Claim.** For every $\epsilon>0$, if $c=\sqrt{\max(0,\log(2/\epsilon)/2)}$, then $2\exp(-2c^2)\leq\epsilon$.

**Proof.** Split into two cases. If $2\leq\epsilon$, then $c^2\geq0$, so $\exp(-2c^2)\leq1$ and consequently $2\exp(-2c^2)\leq2\leq\epsilon$. If $\epsilon<2$, then $2/\epsilon>1$ and $\log(2/\epsilon)>0$. Thus the maximum in the definition of $c$ is its logarithmic term, and $c^2=\log(2/\epsilon)/2$. It follows that $\exp(-2c^2)=\exp(-\log(2/\epsilon))=\epsilon/2$, giving equality in the desired bound.
