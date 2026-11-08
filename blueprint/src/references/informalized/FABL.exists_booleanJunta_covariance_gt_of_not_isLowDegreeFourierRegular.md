<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityCharacterizations.lean :: FABL.exists_booleanJunta_covariance_gt_of_not_isLowDegreeFourierRegular -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A junta with large covariance

**Claim.** If $f$ is not $(\varepsilon,k)$-regular, then some Boolean-valued $k$-junta $h$ satisfies $\operatorname{Cov}[f,h]>\varepsilon$.

**Proof.** Failure of regularity gives a nonempty coordinate set $S$ of size at most $k$ whose Fourier coefficient has absolute value greater than $\varepsilon$. Take the parity function on $S$. It depends only on coordinates in $S$, so it is a $k$-junta. The covariance Fourier expansion and the fact that the Fourier coefficients of a parity monomial vanish except at its matching set show that the covariance of $f$ with this parity function is exactly the Fourier coefficient of $f$ at $S$ ($\mathrm{covariance\_eq\_sum\_fourierCoeff\_mul}$, $\mathrm{parityFunction\_toReal}$, and $\mathrm{fourierCoeff\_monomial}$). If this coefficient is nonnegative, its absolute-value bound gives covariance greater than $\varepsilon$. If it is negative, negate the parity function. Negation preserves dependence on $S$; its real-valued form is the negative monomial ($\mathrm{BooleanFunction.toReal\_neg}$), and covariance changes sign when its second argument is negated ($\mathrm{covariance\_neg\_right}$). The resulting covariance is again the absolute value of the coefficient and is greater than $\varepsilon$.

**Key facts.** `FABL.parityFunction_toReal`, `FABL.covariance_eq_sum_fourierCoeff_mul`, `FABL.fourierCoeff_monomial`, `FABL.BooleanFunction.toReal_neg`, `FABL.covariance_neg_right`.

**Caveat.** The supplied informal statement also describes a forward covariance bound, but this proof establishes only the stated converse.
