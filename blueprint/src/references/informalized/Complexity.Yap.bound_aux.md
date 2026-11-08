<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.bound_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bound on a Natural Expression

**Claim.** For natural numbers $A,\alpha,n,W,s$, if $n+1\le W$ and $s\le W$, then $A(n+1)^\alpha+2s\le (A+2)W^{\alpha+1}$.

**Proof.** Since $n+1\le W$, we have $1\le W$. Monotonicity of natural-number powers gives $(n+1)^\alpha\le W^\alpha\le W^{\alpha+1}$, where the second inequality uses $1\le W$. The same fact implies $W=W^1\le W^{\alpha+1}$. Multiplying the first bound by $A$ and using $s\le W\le W^{\alpha+1}$ yields $A(n+1)^\alpha+2s\le AW^{\alpha+1}+2W^{\alpha+1}=(A+2)W^{\alpha+1}$.
