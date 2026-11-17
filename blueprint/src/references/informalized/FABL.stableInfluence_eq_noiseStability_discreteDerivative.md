<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.stableInfluence_eq_noiseStability_discreteDerivative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence as Derivative Noise Stability

**Claim.** For $\rho\in[0,1]$, a real-valued function $f$ on the sign cube, and coordinate $i$, its stable influence at $i$ equals the noise stability of its discrete derivative at parameter $\rho$.

**Proof.** Expand noise stability as the Fourier sum $\sum_T \rho^{|T|}\widehat{D_i f}(T)^2$ using the Fourier formula for noise stability (`noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`). The derivative's Fourier coefficient is zero when $i\in T$, and otherwise equals $\widehat f(T\cup\{i\})$ (`fourierCoeff_discreteDerivative`). Hence only sets $T$ not containing $i$ contribute, and the sum becomes $\sum_{T:i\notin T}\rho^{|T|}\widehat f(T\cup\{i\})^2$. Match these sets with the sets $S$ containing $i$ by $S=T\cup\{i\}$; the inverse map is $T=S\setminus\{i\}$. Erasing a member lowers cardinality by one and reinserting it recovers the original set, so each matched term has exponent $|S|-1$ and the same Fourier coefficient. This is precisely the defining sum for stable influence.

**Key facts.** `FABL.noiseStability_eq_sum_rho_pow_mul_sq_fourierCoeff`, `FABL.fourierCoeff_discreteDerivative`.
