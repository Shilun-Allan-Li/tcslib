<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/SmoothVariation.lean :: BooleanAnalysis.GaussianSpace.hasDerivAt_gaussianRotation_comp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Derivative along a Gaussian rotation curve

**Claim.** If $f$ has Fréchet derivative $L$ at $x\in\mathbb R^n$ and $y\in\mathbb R^n$, then $\theta\mapsto f(\cos\theta\,x+\sin\theta\,y)$ has derivative $L(y)$ at $\theta=0$.

**Proof.** Let $\gamma(\theta)=\cos\theta\,x+\sin\theta\,y$, coordinate by coordinate. Since the derivatives of cosine and sine at zero are $0$ and $1$, respectively, $\gamma(0)=x$ and $\gamma'(0)=y$. Applying the chain rule to $f\circ\gamma$ gives derivative $L(\gamma'(0))=L(y)$.
