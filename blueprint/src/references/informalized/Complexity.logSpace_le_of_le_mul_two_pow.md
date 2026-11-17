<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.logSpace_le_of_le_mul_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Log-space bound from an exponential bound

**Claim.** If $v\le A2^s$ and $1\le s$, then $\ell(v)\le(A+1)s$, where $\ell(v)=\lfloor\log_2 v\rfloor+1$ for positive $v$ and $\ell(0)=1$.

**Proof.** First use $A<2^A$ and $s>0$ to obtain $A2^s<2^{A+s}$; hence $v<2^{A+s}$. Also, since $s\ge1$, we have $A+s\le(A+1)s$. If $v=0$, then $\ell(v)=1$, which is at most $(A+1)s$. If $v>0$, the strict exponential bound implies $\lfloor\log_2 v\rfloor<A+s$, so $\ell(v)\le A+s\le(A+1)s$.
