<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/StableInfluence.lean :: FABL.hasDerivAt_stabilityCurve -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability Curve Derivative

**Claim.** For every real-valued cube function, the stability curve is differentiable at each real $\rho$, with derivative $\sum_S |S|\rho^{|S|-1}\widehat f(S)^2$.

**Proof.** The stability curve is a finite sum, indexed by subsets $S$, of terms $\rho^{|S|}\widehat f(S)^2$. Differentiate each term: the power rule gives $|S|\rho^{|S|-1}$, and the Fourier coefficient squared is constant with respect to $\rho$. Differentiation commutes with this finite sum, so summing these termwise derivatives gives the stated formula.
