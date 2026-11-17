<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Basic.lean :: BooleanAnalysis.Hypercontractivity.lp_interpolation_cancel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scalar Interpolation Cancellation

**Claim.** If $A\ge0$, $M>0$, $u>0$, $u+v=2$, and $M^2\le A^u(e^cM)^v$, then $M\le e^{cv/u}A$.

**Proof.** First $A$ must be strictly positive: if $A=0$, then $A^u=0$ because $u>0$, making the right side of the assumed bound zero, contrary to $M^2>0$. Both sides of the bound are therefore positive, so monotonicity of the logarithm applies. Taking logarithms, and using $\log(x^s)=s\log x$ for positive $x$, gives $2\log M\le u\log A+v(c+\log M)$. Using $u+v=2$ and rearranging yields $u(\log M-\log A)\le cv$. Division by $u>0$ gives $\log M-\log A\le cv/u$. Add $\log A$ and exponentiate; because the exponential is increasing and $A>0$, this becomes $M\le e^{cv/u}A$.
