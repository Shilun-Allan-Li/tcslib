<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.exists_two_div_pi_upper_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The level-one upper bound

**Claim.** There is a positive constant $C$ such that every Boolean function with singleton Fourier coefficients bounded by $\varepsilon$ has level-one Fourier weight at most $2/\pi+C\varepsilon$.

**Proof.** Take a constant $C_0>0$ from the estimate that a normalized linear form with small coefficients has expected absolute value within $C_0$ times the coefficient bound of $\sqrt{2/\pi}$ (`exists_expect_abs_linearForm_sub_sqrt_two_div_pi_le_of_regular`). Set $C=4(1+C_0+C_0^2)$. Fix a function and an admissible $\varepsilon$, and write $a_i=\widehat f(i)$ and $W=W^1[f]$. The level-one identities say that $W=\sum_i a_i^2$ and that $W\in[0,1]$ (`fourierWeightAtLevel_one_eq_sum_singleton`, `fourierWeightAtLevel_one_mem_Icc`). If $W\le1/4$, then $W\le2/\pi$; adding the nonnegative error term proves the result. Otherwise set $\sigma=\sqrt W>1/2$ and $b_i=a_i/\sigma$. Then $\sum_i b_i^2=1$, and $|b_i|\le2\varepsilon$. The linear-form estimate therefore gives $\mathbb E|\sum_i b_i x_i|\le q+2C_0\varepsilon$, where $q=\sqrt{2/\pi}$. The identity for the expected product of a function and a linear form (`expect_mul_linearForm_eq`) gives $\mathbb E[f(x)\sum_i b_i x_i]=\sum_i b_i a_i=W/\sigma=\sigma$. Since $f(x)$ is either $1$ or $-1$ (`signValue_one`, `signValue_neg_one`), pointwise $f(x)\sum_i b_i x_i\le|\sum_i b_i x_i|$. Hence $\sigma\le q+2C_0\varepsilon$. Squaring this nonnegative inequality and using $\varepsilon^2\le\varepsilon$, $q\le1$, and $q^2=2/\pi$ yields $W\le2/\pi+(4C_0+4C_0^2)\varepsilon$. The chosen $C$ is at least that coefficient, completing the bound.

**Key facts.** `FABL.exists_expect_abs_linearForm_sub_sqrt_two_div_pi_le_of_regular`, `FABL.fourierWeightAtLevel_one_mem_Icc`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.expect_mul_linearForm_eq`, `FABL.signValue_one`, `FABL.signValue_neg_one`.
