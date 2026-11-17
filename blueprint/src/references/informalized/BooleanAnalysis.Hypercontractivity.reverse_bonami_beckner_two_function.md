<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/Reverse/TwoFunction.lean :: BooleanAnalysis.Hypercontractivity.reverse_bonami_beckner_two_function -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-function reverse hypercontractivity

**Claim.** If $p,q<1$, $0\le\rho\le1$, and $\rho^2\le(1-p)(1-q)$, then for nonnegative functions $f,g$ on the Boolean cube, $\langle f,T_\rho g\rangle\ge M_p(f)M_q(g)$.

**Proof.** First note that every extended power mean is nonnegative. Also, for a nonnegative function $u$, $M_0(u)\le \mathbb E u$: this follows from monotonicity of the extended means up to exponent $1$, together with $M_1(u)=\mathbb E u$. When both exponents are zero, the result follows from the zero-exponent reverse Hölder inequality: $\langle u,v\rangle\ge M_0(u)M_0(v)$. If either function vanishes somewhere, the corresponding zero mean is zero and nonnegativity of the inner product gives the claim; otherwise apply $M_0(w)\le\mathbb E w$ to $w=uv$ and use $M_0(uv)=M_0(u)M_0(v)$.

For the main case, suppose $p\ne0$. Set $c=p/(p-1)$ and $d=1-\rho^2/(1-p)$. Since $p<1$, $1-p>0$ and $c<1$. The assumed constraint gives $q\le d$, while $\rho^2\le1$ gives $c\le d\le1$. Moreover, direct algebra yields $(1-d)/(1-c)=\rho^2$. Apply reverse Hölder at exponent $p$ to $f$ and $T_\rho g$, which is nonnegative by preservation of nonnegativity under the noise operator. Then apply the one-function reverse Bonami–Beckner inequality with exponents $d,c$ to $g$, and use monotonicity of the extended means from $q$ to $d$. These give $M_c(T_\rho g)\ge M_q(g)$, so multiplying by the nonnegative $M_p(f)$ proves the desired bound.

The only remaining case has $p=0$. If also $q=0$, use the zero-exponent case just established and the one-function reverse Bonami–Beckner inequality at exponents $0,0$ for $g$. If $q\ne0$, apply the main case with the roles of $f,g$ and the exponents $q,0$ interchanged; the constraint supplies $\rho^2\le(1-q)(1-0)$. Symmetry of the inner product and self-adjointness of the noise operator identify the resulting inner product with $\langle f,T_\rho g\rangle$.

**Key facts.** `BooleanAnalysis.Hypercontractivity.lpMean_exponent_mono`, `BooleanAnalysis.Hypercontractivity.lpMean_of_pos`, `BooleanAnalysis.expect_eq_fintypeExpect`, `BooleanAnalysis.Hypercontractivity.noiseOp_nonneg`, `BooleanAnalysis.Hypercontractivity.reverse_holder`, `BooleanAnalysis.Hypercontractivity.reverse_bonami_beckner`, `BooleanAnalysis.innerProduct_comm`, `BooleanAnalysis.noiseOp_self_adjoint`.
