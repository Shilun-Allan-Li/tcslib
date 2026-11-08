<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.isPmfTwoEvenHypercontractive_necessary_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Necessary hypercontractive bound

**Claim.** Under the stated normalization, odd-moment, and hypercontractivity assumptions, one has $\rho^2\le 1/(2r-1)$.

**Proof.** The first odd-moment condition gives $\mathbb E_\mu[X]=0$. For each positive integer $m$, set $t_m=1/(m+1)$; these numbers are positive and tend to zero. Apply hypercontractivity with $a=1$ and $b=t_m$, raise both sides to the even power $2r$, and use the even-power formula for the $2r$-norm and the centered, normalized formula for the $2$-norm (FABL.pmfLpNorm_even_pow_eq_pmfExpectation_even, FABL.pmfLpNorm_two_affine_centered). Expanding the resulting moment by the vanishing odd moments gives a sum over even powers of $X$ (FABL.pmfExpectation_affine_evenMoment_of_oddMoments). Every term in this sum is nonnegative; retaining only its constant and quadratic terms, and using $\mathbb E[X^2]=1$, yields
\[
1+\binom{2r}{2}(\rho t_m)^2\le (1+t_m^2)^r.
\]
Subtract $1$ and divide by $t_m^2>0$. As $m$ tends to infinity, the right-hand quotient tends to $r$, the derivative at zero of $u\mapsto(1+u)^r$. Hence $\binom{2r}{2}\rho^2\le r$. Since $\binom{2r}{2}=r(2r-1)$ and $r>0$, cancellation gives the required bound.

**Key facts.** `FABL.pmfLpNorm_nonneg`, `FABL.pmfLpNorm_even_pow_eq_pmfExpectation_even`, `FABL.pmfLpNorm_two_affine_centered`, `FABL.pmfExpectation_affine_evenMoment_of_oddMoments`, `FABL.pmfExpectation_const`, `FABL.pmfExpectation_nonneg`.
