<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Hoeffding.lean :: bernoulli_mgf_bound_step2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of the auxiliary derivative expression

**Claim.** When $1-L+Le^{-x}>0$, the derivative at $x$ of $y\mapsto-L+y/4+Le^{-y}/(1-L+Le^{-y})$ equals $1/4-L(1-L)e^{-x}/(1-L+Le^{-x})^2$.

**Proof.** The constant term differentiates to zero and $y/4$ contributes $1/4$. For the quotient, apply the quotient rule to numerator $Le^{-y}$ and denominator $1-L+Le^{-y}$. Their derivatives are both $-Le^{-y}$, so the quotient derivative simplifies to $-L(1-L)e^{-y}/(1-L+Le^{-y})^2$. Evaluating at $y=x$ gives the formula; positivity of the denominator follows from the hypothesis.
