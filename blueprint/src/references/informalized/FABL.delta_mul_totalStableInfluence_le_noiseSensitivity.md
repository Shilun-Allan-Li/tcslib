<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LTFNoiseSensitivityDerivative.lean :: FABL.delta_mul_totalStableInfluence_le_noiseSensitivity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence and Noise Sensitivity

**Claim.** For $0<\delta\le\tfrac12$, $\delta$ times the total stable influence of the real-valued sign version of $f$, at correlation $1-2\delta$, is at most the noise sensitivity of $f$ at rate $\delta$.

**Proof.** First double both sides. Express the total stable influence as a sum over subsets $S$, with each term $(|S|)(1-2\delta)^{|S|-1}\widehat f(S)^2$ (\texttt{totalStableInfluence\_eq\_sum\_card\_mul\_rho\_pow\_mul\_sq\_fourierCoeff}), and express twice the noise sensitivity as the sum with terms $\bigl(1-(1-2\delta)^{|S|}\bigr)\widehat f(S)^2$ (\texttt{two\_mul\_noiseSensitivity\_eq\_sum\_fourier}). For each subset, the scalar inequality $2\delta |S|(1-2\delta)^{|S|-1}\le 1-(1-2\delta)^{|S|}$ holds under $0\le\delta\le\tfrac12$ (\texttt{two\_mul\_delta\_mul\_card\_mul\_pow\_le\_one\_sub\_pow}). Multiplying it by the nonnegative square $\widehat f(S)^2$ preserves the inequality. Summing gives the doubled claim, and dividing by $2$ yields the result.

**Key facts.** `FABL.totalStableInfluence_eq_sum_card_mul_rho_pow_mul_sq_fourierCoeff`, `FABL.two_mul_noiseSensitivity_eq_sum_fourier`, `FABL.two_mul_delta_mul_card_mul_pow_le_one_sub_pow`.
