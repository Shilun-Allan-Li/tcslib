<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RandomBooleanFourierMaximum.lean :: FABL.two_pow_two_mul_add_one_lt_exp_two_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound

**Claim.** For every integer $n\ge2$, $2^{2n+1}<\exp(2n)$.

**Proof.** First, $4<e^2$: since $e>2$, squaring gives this inequality. Also $32<e^4$: the elementary lower bound $e>8/3$ gives $(8/3)^4>32$, hence $e^4>32$. Write $n=2+k$ with $k\ge0$. Then $2^{2n+1}=32\cdot4^k<e^4\cdot4^k$. From $4<e^2$ we get $4^k\le e^{2k}$, so the expression is at most bounded by $e^4e^{2k}=e^{2n}$. Together these inequalities give the strict claim.
