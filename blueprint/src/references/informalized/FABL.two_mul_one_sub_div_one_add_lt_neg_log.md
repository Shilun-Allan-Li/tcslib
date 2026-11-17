<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.two_mul_one_sub_div_one_add_lt_neg_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic inequality on the unit interval

**Claim.** For every real number $x$ with $0<x<1$, $\frac{2(1-x)}{1+x}<-\log x$.

**Proof.** Set $y=(1-x)/(1+x)$. The hypotheses imply $0<y<1$. The logarithmic series bound for $0\le y<1$ states that $\sum_{i=0}^{1}y^{2i+1}/(2i+1)\le\tfrac12\log((1+y)/(1-y))$ (\texttt{Real.sum_range_le_log_div}). The sum on the left is $y+y^3/3$, which is strictly greater than $y$ because $y>0$. Substitution of the definition of $y$ gives $(1+y)/(1-y)=1/x$. Thus $y<\tfrac12\log(1/x)=-\tfrac12\log x$. Multiplying by $2$ and replacing $y$ by its expression in $x$ proves the claim.
