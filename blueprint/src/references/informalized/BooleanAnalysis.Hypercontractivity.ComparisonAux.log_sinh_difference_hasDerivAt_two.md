<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.log_sinh_difference_hasDerivAt_two -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a logarithmic hyperbolic-sine difference

**Claim.** For each $u>0$, the function $q\mapsto(\log(\sinh(u/q))-\log(\sinh(u-u/q)))/2$ is differentiable at $q=2$ with derivative $-u\cosh(u/2)/(4\sinh(u/2))$.

**Proof.** At $q=2$, both hyperbolic-sine arguments equal $u/2>0$, so their hyperbolic sines are positive and the logarithms are differentiable there. The function $q\mapsto u/q$ has derivative $-u/4$ at $2$. By the chain rule, the derivative of $\log(\sinh(u/q))$ there is $\coth(u/2)(-u/4)$. The second argument is $u-u/q$, whose derivative at $2$ is $u/4$; therefore the derivative of $\log(\sinh(u-u/q))$ is $\coth(u/2)(u/4)$. Subtracting these derivatives and dividing by $2$ gives $-u\coth(u/2)/4=-u\cosh(u/2)/(4\sinh(u/2))$.
