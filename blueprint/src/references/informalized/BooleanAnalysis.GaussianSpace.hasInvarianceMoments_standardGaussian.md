<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.hasInvarianceMoments_standardGaussian -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance moments of the standard Gaussian

**Claim.** The identity random variable under standard Gaussian measure has the invariance moment conditions: it is $9$-reasonable, has mean zero, second moment one, and third moment zero.

**Proof.** The standard Gaussian law is a probability measure, and $9\ge1$. Its identity random variable belongs to $L^4$, as follows from the Gaussian integrability result for the identity at variance one. Its fourth moment is $3$ and its second moment is $1$, so the fourth-moment bound required for $9$-reasonability holds. The mean is zero by symmetry of the centered Gaussian. The second and third moments are respectively $1$ and $0$, by the standard Gaussian moment identities (\texttt{integral\_second\_standardGaussian}, \texttt{integral\_third\_standardGaussian}); the fourth-moment identity used above is \texttt{integral\_fourth\_standardGaussian}.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_fourth_standardGaussian`, `BooleanAnalysis.GaussianSpace.integral_second_standardGaussian`, `BooleanAnalysis.GaussianSpace.integral_third_standardGaussian`.

**Caveat.** The supplied informal statement describes several different input distributions, but the formal declaration and proof establish only the standard Gaussian case.
