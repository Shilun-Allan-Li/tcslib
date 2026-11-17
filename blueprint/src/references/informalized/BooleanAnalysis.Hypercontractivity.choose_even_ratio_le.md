<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoPoint.lean :: BooleanAnalysis.Hypercontractivity.choose_even_ratio_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even binomial coefficient comparison

**Claim.** Under the stated assumptions on $p,q,\rho$, for every integer $k\ge1$ the generalized binomial coefficients satisfy $\binom{p}{2k}\le(p/q)\binom{q}{2k}\rho^{2k}$.

**Proof.** Proceed by induction on $k$. The case $k=1$ follows by writing each second generalized binomial coefficient as $s(s-1)/2$ (\texttt{ring\_choose\_two}) and substituting $\rho^2=(1-p)/(1-q)$; the assumptions $q>0$ and $q<1$ justify clearing the denominators, after which the inequality follows by elementary algebra. For the successor step, apply the even-ratio successor comparison (\texttt{choose\_even\_ratio\_step}) with $K=k$. Its hypotheses are the induction bound and the original assumptions, and it gives exactly the required inequality at $k+1$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.ring_choose_two`, `BooleanAnalysis.Hypercontractivity.choose_even_ratio_step`.
