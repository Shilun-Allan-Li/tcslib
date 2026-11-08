<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLpInequalities.lean :: FABL.pmfExpectation_abs_sub_mean_rpow_le_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Deviation Moment Bound

**Claim.** For a sign-valued function and $1\le p\le2$, its absolute deviation moment of order $p$ is at most its variance.

**Proof.** Let $a$ and $b$ be the masses of the values $1$ and $-1$. They are nonnegative (\texttt{pmfSignPlusMass\_nonneg}, \texttt{pmfSignMinusMass\_nonneg}) and satisfy $a+b=1$ (\texttt{pmfSignPlusMass\_add\_minus}). The exact formulas for the absolute moment and variance (\texttt{pmfExpectation\_abs\_sub\_mean\_rpow} and \texttt{pmfExpectation\_sq\_sub\_mean}) reduce the claim to $a(2b)^p+b(2a)^p\le4ab$. If either mass is zero, the other is one, and both sides are zero; here $p>0$ ensures the zero powers vanish. Otherwise both masses are positive. Set $r=p-1$, so $0\le r\le1$. The inequality $(2)^{r-1}(a^r+b^r)\le1$ (\texttt{two\_rpow\_sub\_one\_mul\_add\_rpow\_le\_one}) bounds the expression after rewriting it as $4ab$ times that factor: use $2^p=4\cdot2^{p-2}$ and $a^p=a\,a^{p-1}$, $b^p=b\,b^{p-1}$. Since $4ab\ge0$, this proves the desired inequality.

**Key facts.** `FABL.pmfSignPlusMass_nonneg`, `FABL.pmfSignMinusMass_nonneg`, `FABL.pmfSignPlusMass_add_minus`, `FABL.pmfExpectation_abs_sub_mean_rpow`, `FABL.pmfExpectation_sq_sub_mean`, `FABL.two_rpow_sub_one_mul_add_rpow_le_one`.
