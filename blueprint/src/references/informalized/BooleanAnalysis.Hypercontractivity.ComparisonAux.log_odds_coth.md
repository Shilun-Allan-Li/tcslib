<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Comparison.lean :: BooleanAnalysis.Hypercontractivity.ComparisonAux.log_odds_coth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hyperbolic ratio of the log odds

**Claim.** For $0<\lambda<1/2$, the ratio $\cosh\!\left(\frac12\log\frac{1-\lambda}{\lambda}\right)/\sinh\!\left(\frac12\log\frac{1-\lambda}{\lambda}\right)$ equals $1/(1-2\lambda)$.

**Proof.** Put $v=\frac12\log((1-\lambda)/\lambda)$. The hypotheses imply $(1-\lambda)/\lambda>1$, hence $v>0$; in particular $\sinh v\ne0$. They also give $1-2\lambda\ne0$. The exponential identity $e^v=((1-\lambda)/\lambda)e^{-v}$ follows because $v=\log((1-\lambda)/\lambda)-v$. Multiplying by $\lambda$ gives $\lambda e^v=(1-\lambda)e^{-v}$. Using $\cosh v=(e^v+e^{-v})/2$ and $\sinh v=(e^v-e^{-v})/2$, this linear relation yields $(1-2\lambda)\cosh v=\sinh v$. Division by the two nonzero denominators proves the claimed ratio.
