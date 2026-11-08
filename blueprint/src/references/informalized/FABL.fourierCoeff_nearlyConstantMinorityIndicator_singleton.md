<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.fourierCoeff_nearlyConstantMinorityIndicator_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minority Indicator Singleton Coefficient

**Claim.** At a singleton coordinate, the Fourier coefficient of the nearly constant minority indicator is minus one half the original coefficient when the mean is nonnegative, and one half the original coefficient when the mean is negative.

**Proof.** Split according to whether the mean of $f$ is nonnegative. In the first case the indicator is $(1-f)/2$. Multiplying by the singleton monomial gives $(\chi_{\{i\}}-f\chi_{\{i\}})/2$. Taking expectations, the first term vanishes because a nonempty monomial has mean zero (\(\texttt{FABL.expect_monomial}\)); the second is the negative of the original singleton Fourier coefficient, divided by two. In the second case the indicator is $(1+f)/2$, so the same calculation has a plus sign on the original coefficient. The constant monomial contribution again has expectation zero.

**Key facts.** `FABL.expect_monomial`.
