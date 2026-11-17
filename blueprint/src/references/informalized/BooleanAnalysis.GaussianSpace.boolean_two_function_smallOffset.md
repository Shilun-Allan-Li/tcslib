<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Noise/BooleanBounds.lean :: BooleanAnalysis.GaussianSpace.boolean_two_function_smallOffset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-function inequality for small offset

**Claim.** Under the stated assumptions on $r,s,\rho$, the inner product of $f$ with the noise operator applied to $g$ is bounded by the product of their respective $(1+r)$ and $(1+s)$ moment norms.

**Proof.** Set $u=(1+r)/r$. Since $r>0$ and $rs\le1$, we have $u\ge2$ and $1+s\le u$. The exponent identities $u-1=1/r$, $u/(u-1)=1+r$, and $(u-1)/u=1/(1+r)$ hold by elementary algebra; also $(1+s-1)/(u-1)=rs$. Consequently, $\rho^2\le rs$ and $\rho\ge0$ imply $\rho\le\sqrt{(1+s-1)/(u-1)}$. Apply the general two-function hypercontractive inequality with input exponent $p=1+s$ and output parameter $u$. Its hypotheses hold by the preceding bounds and $\rho\le1$. The resulting two moment exponents are $u/(u-1)=1+r$ and $p=1+s$, with outer powers $(u-1)/u=1/(1+r)$ and $1/p=1/(1+s)$. Substitution gives the claimed inequality.

**Key facts.** `BooleanAnalysis.Hypercontractivity.general_two_function_hypercontractivity`.
