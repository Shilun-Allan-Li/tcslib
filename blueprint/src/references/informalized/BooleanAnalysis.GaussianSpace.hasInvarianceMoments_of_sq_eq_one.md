<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/InputMoments.lean :: BooleanAnalysis.GaussianSpace.hasInvarianceMoments_of_sq_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Moments of a sign-valued variable

**Claim.** If $X$ has mean zero on a probability space and $X(\omega)^2=1$ everywhere, then it satisfies the invariance moment conditions: it is $9$-reasonable, has second moment one, and has third moment zero.

**Proof.** Squaring $X(\omega)^2=1$ gives $X(\omega)^4=1$. Also $X(\omega)^2=1$ implies $-1\le X(\omega)\le1$, so $|X(\omega)|\le1$. Almost-everywhere strong measurability and this uniform bound imply that $X$ belongs to $L^4$. The fourth moment is $1$, while the second moment is $1$; consequently the required fourth-moment bound holds, since $1\le9\cdot1^2$. The probability-space condition and the lower bound $1\le9$ complete the $9$-reasonability property. The first moment is the assumed zero mean. The second moment equals $1$ because the integrand is constantly one and the measure is a probability measure. Finally, $X^3=X\cdot X^2=X$ pointwise, so the third moment equals the first and is zero.
