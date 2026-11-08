<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/UnateFunctions.lean :: FABL.abs_fourierCoeff_singleton_eq_influence_iff_isUnateInCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton coefficient detects coordinate unateness

**Claim.** The absolute value of the singleton Fourier coefficient equals the influence in coordinate $i$ if and only if the Boolean function is monotone or antimonotone in that coordinate.

**Proof.** First identify the singleton coefficient with the mean of the discrete derivative (`mean_discreteDerivative_eq_fourierCoeff_singleton`). The influence is the mean of the squared derivative. For a Boolean function, the derivative at each point can only take the values $-1,0,1$, as follows directly from its difference formula (`discreteDerivative_apply`) and the two possible function values. Consequently, $D^2-D\geq0$ and $D^2+D\geq0$ pointwise; these are the two derivative inequalities recorded by `derivative_sq_sub_self_nonneg` and `derivative_sq_add_self_nonneg`.

Suppose first that the absolute mean derivative equals the mean squared derivative. If the mean derivative is nonnegative, the mean of $D^2-D$ is zero. Since this integrand is pointwise nonnegative on the finite cube, it vanishes everywhere. Thus each derivative is either $0$ or $1$, which says the function does not decrease when coordinate $i$ changes from $-1$ to $1$: it is monotone in that coordinate. If the mean derivative is negative, apply the same reasoning to $D^2+D$: its mean is zero, so every derivative is either $0$ or $-1$, and the function is antimonotone.

Conversely, if the function is monotone in coordinate $i$, its Boolean values and monotonicity force each derivative to be $0$ or $1$. Hence $D^2=D$, so the mean squared derivative equals the mean derivative, which is nonnegative; its absolute value is therefore the influence. If the function is antimonotone, each derivative is $0$ or $-1$, so $D^2=-D$ and the mean derivative is nonpositive. The absolute value of that mean again equals the mean squared derivative. Using the singleton-coefficient identity completes both directions.

**Key facts.** `FABL.mean_discreteDerivative_eq_fourierCoeff_singleton`, `FABL.derivative_sq_sub_self_nonneg`, `FABL.derivative_sq_add_self_nonneg`, `FABL.discreteDerivative_apply`.
