<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BlockCharacteristic.lean :: BooleanAnalysis.GaussianSpace.integral_exp_correlatedGaussianMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correlated Gaussian characteristic function

**Claim.** For $\rho\in[-1,1]$ and vectors $a,b\in\mathbb R^n$, the characteristic function of the linear form $\sum_i(a_iX_i+b_iY_i)$ under the correlated Gaussian law is $\exp\bigl(-\tfrac12\sum_i(a_i^2+b_i^2+2\rho a_ib_i)\bigr)$.

**Proof.** Set $s=\sqrt{1-\rho^2}$, so $s^2+\rho^2=1$. Pull the integral back through the map $(x,w)\mapsto(x,\rho x+sw)$ defining the joint law. The phase then splits: its linear form is $\sum_i(a_i+\rho b_i)x_i+\sum_i(sb_i)w_i$, so the complex exponential factors into one function of $x$ and one of $w$. The product measure makes the integral the product of the two Gaussian characteristic functions. By the product Gaussian characteristic-function formula (\texttt{integral_exp_mul_I_gaussianPi}), these factors are exponentials with exponents $-\tfrac12\sum_i(a_i+\rho b_i)^2$ and $-\tfrac12\sum_i(sb_i)^2$. Combining them and using $s^2+\rho^2=1$ gives $-\tfrac12\sum_i(a_i^2+b_i^2+2\rho a_ib_i)$, as required.

**Key facts.** `BooleanAnalysis.GaussianSpace.integral_exp_mul_I_gaussianPi`.
