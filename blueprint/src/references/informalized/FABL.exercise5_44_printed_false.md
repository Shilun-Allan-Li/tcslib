<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.exercise5_44_printed_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of the printed level-one bound

**Claim.** There is an $\alpha\in(0,1/2)$ such that, for every proposed constant $C_\alpha$, one can find a Boolean-cube function with mean absolute value at most $\alpha$ and all level-one Fourier coefficients bounded by a nonnegative $\varepsilon$, yet with level-one Fourier weight greater than $U(\alpha)^2+C_\alpha\varepsilon$.

**Proof.** Choose $\alpha$ with $1/4<\alpha<1/2$ and $U(\alpha)<2U(1/8)$; such a choice is supplied by \texttt{FABL.exists\_signedHammingTwoTail\_alpha}. Regard this as a point of the unit interval. Fix any real $C_\alpha$. Set $\beta=1/8$ and let $t$ be the Gaussian upper quantile at tail probability $\beta$. The quantile identity (\texttt{FABL.standardGaussianUpperTail\_quantile}) gives Gaussian upper tail $\beta$ at $t$. Since the upper tail at zero is $1/2$ and is strictly decreasing (\texttt{FABL.standardGaussianUpperTail\_neg}, \texttt{FABL.standardGaussianUpperTail\_strictAnti}), it follows that $t>0$.

The Gaussian isoperimetric profile at $\beta$ equals the Gaussian density at its corresponding quantile (\texttt{FABL.gaussianIsoperimetricReal\_apply\_of\_mem\_Ioo}). By the choice of $\alpha$, positivity of the profile, and this identity, we have $U(\alpha)^2<4\,\varphi(t)^2$, where $\varphi(t)$ denotes the standard Gaussian density at $t$.

Now consider the signed Hamming two-tail functions on cubes of dimension $m+1$ as $m$ tends to infinity. Their expected absolute values converge to $2\beta=1/4$ (\texttt{FABL.tendsto\_expect\_abs\_signedHammingTwoTail}); their level-one Fourier weights converge to $4\varphi(t)^2$ (\texttt{FABL.tendsto\_fourierWeightAtLevel\_one\_signedHammingTwoTail}); and their common absolute level-one Fourier coefficient, denoted $\varepsilon_m$, tends to zero (\texttt{FABL.abs\_fourierCoeff\_signedHammingTwoTail\_eq\_epsilon}, \texttt{FABL.tendsto\_signedHammingTwoTailEpsilon}). Therefore the expected absolute value is eventually less than $\alpha$. Also, the difference between the level-one weight and $C_\alpha\varepsilon_m$ converges to $4\varphi(t)^2$, which is strictly larger than $U(\alpha)^2$. It is consequently eventually larger than $U(\alpha)^2$. Choose an index $m$ where both eventual properties hold, and take the corresponding function and $\varepsilon_m$.

The function takes values in $[-1,1]$ by \texttt{FABL.signedHammingTwoTail\_mem\_Icc}. Every level-one coefficient has absolute value exactly $\varepsilon_m$ by \texttt{FABL.abs\_fourierCoeff\_signedHammingTwoTail\_eq\_epsilon}, and $\varepsilon_m\ge0$. The chosen strict inequality gives the claimed violation.

**Key facts.** `FABL.exists_signedHammingTwoTail_alpha`, `FABL.standardGaussianUpperTail_quantile`, `FABL.standardGaussianUpperTail_neg`, `FABL.standardGaussianUpperTail_strictAnti`, `FABL.gaussianIsoperimetricReal_apply_of_mem_Ioo`, `FABL.gaussianIsoperimetricReal_pos`, `FABL.tendsto_expect_abs_signedHammingTwoTail`, `FABL.tendsto_signedHammingTwoTailEpsilon`, `FABL.tendsto_fourierWeightAtLevel_one_signedHammingTwoTail`, `FABL.signedHammingTwoTail_mem_Icc`, `FABL.abs_fourierCoeff_signedHammingTwoTail_eq_epsilon`, `FABL.gaussianIsoperimetricReal_eq_gaussianIsoperimetric`.
