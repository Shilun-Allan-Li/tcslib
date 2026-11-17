<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.deriv_stabilityCurve_eq_totalStableInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the stability curve

**Claim.** For every real parameter $\rho$ and real-valued cube function $f$, the derivative of the stability curve at $\rho$ equals the total stable influence at $\rho$.

**Proof.** The stability curve is the finite sum of terms $\rho^{|S|}\widehat f(S)^2$. Its derivative is the sum $\sum_S |S|\rho^{|S|-1}\widehat f(S)^2$, by the established derivative formula for the stability curve ($\texttt{FABL.hasDerivAt\_stabilityCurve}$). The total stable influence has exactly this same sum representation ($\texttt{FABL.totalStableInfluence\_eq\_sum\_card\_mul\_rho\_pow\_mul\_sq\_fourierCoeff}$), so the two quantities are equal.

**Key facts.** `FABL.hasDerivAt_stabilityCurve`, `FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`.
