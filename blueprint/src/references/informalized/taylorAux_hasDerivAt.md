<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/JohnsonLindenstrauss/ChiSquaredMGF.lean :: taylorAux_hasDerivAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative of a Taylor auxiliary function

**Claim.** For $h(x)=x^2+x+\log(1-x)$, every $u<1$ is a differentiability point and $h'(u)=u(1-2u)/(1-u)$.

**Proof.** Because $u<1$, the denominator $1-u$ is nonzero. The derivatives at $u$ of $x^2$, $x$, and $1-x$ are respectively $2u$, $1$, and $-1$. The chain rule for the logarithm therefore gives derivative $-1/(1-u)$ for $\log(1-x)$. Adding these derivatives yields $2u+1-1/(1-u)$. Putting this over the common denominator $1-u$ and simplifying gives $u(1-2u)/(1-u)$, as claimed.
