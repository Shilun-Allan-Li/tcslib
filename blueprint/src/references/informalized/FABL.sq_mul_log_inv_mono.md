<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/NearlyConstantLevelOne.lean :: FABL.sq_mul_log_inv_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of a Logarithmic Expression

**Claim.** If $0<x\le y\le\tfrac12$, then $x^2\log(1/x)\le y^2\log(1/y)$.

**Proof.** The assumptions give $0<x\le y\le\tfrac12$. Thus $x^2\le y^2$, and both squares lie in $[0,e^{-1}]$. On this interval the function $u\mapsto u\log u$ is antitone, so $y^2\log(y^2)\le x^2\log(x^2)$. For every positive $z$, logarithm laws give $z^2\log(1/z)=-\tfrac12 z^2\log(z^2)$. Applying this identity at $x$ and $y$ and negating the preceding inequality, then multiplying by $\tfrac12>0$, yields the claim.
