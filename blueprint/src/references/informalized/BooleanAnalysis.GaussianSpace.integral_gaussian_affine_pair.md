<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/Kernel.lean :: BooleanAnalysis.GaussianSpace.integral_gaussian_affine_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gaussian affine integral identity

**Claim.** Under the stated conditions on $b,c,v$, integrating $f(a+bZ+cW)$ over independent standard Gaussian vectors gives the same integral as integrating $f(a+vY)$ over a standard Gaussian vector.

**Proof.** First, if $v=0$, the identity $b^2+c^2=v^2$ forces $b=c=0$, so both integrands are the constant $f(a)$ and the probability measures give equal integrals. Otherwise divide the quadratic identity by $v^2$ to obtain $(b/v)^2+(c/v)^2=1$; also $c/v\ge 0$. The Gaussian combination measure-preservation result (`measurePreserving_gaussianCombination`) says that $(b/v)Z+(c/v)W$ has the standard product Gaussian law. Apply it to the function $g(y)=f(a+vy)$, which is strongly measurable because it is the composition of $f$ with the affine map. Pointwise, $g((b/v)Z+(c/v)W)=f(a+bZ+cW)$; measure preservation therefore identifies the two integrals.

**Key facts.** `BooleanAnalysis.GaussianSpace.measurePreserving_gaussianCombination`.
