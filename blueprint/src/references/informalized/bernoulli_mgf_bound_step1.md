<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: bernoulli_mgf_bound_step1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the auxiliary function

**Claim.** When $1-L+Le^{-x}>0$, the function $\varphi(y)=-Ly+y^2/8-\ln(1-Le^{-y})$ (with the logarithm's argument understood as $1-L+Le^{-y}$) has derivative at $x$ equal to $-L+x/4+Le^{-x}/(1-L+Le^{-x})$.

**Proof.** Differentiate the linear term to obtain $-L$ and the quadratic term to obtain $x/4$. For the logarithmic term, the chain rule gives the derivative of its argument, $-Le^{-x}$, divided by $1-L+Le^{-x}$; the outer subtraction changes this contribution to $Le^{-x}/(1-L+Le^{-x})$. The assumed positivity ensures the logarithm is differentiable at the point.
