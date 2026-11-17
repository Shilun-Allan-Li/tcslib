<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Cube.lean :: BooleanAnalysis.GaussianSpace.derivative_linear_combination -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of the discrete derivative

**Claim.** The discrete derivative in coordinate $i$ of $x\mapsto cf(x)+dg(x)$ is $x\mapsto c(D_i f)(x)+d(D_i g)(x)$.

**Proof.** Regard the pointwise linear combination as $c f+d g$. The derivative is additive, so its value on this sum is the sum of the derivatives of $cf$ and $dg$. It also commutes with scalar multiplication, giving $cD_i f+dD_i g$ pointwise.

**Key facts.** `BooleanAnalysis.derivative_add`, `BooleanAnalysis.derivative_smul`.
