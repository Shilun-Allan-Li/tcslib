<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.arcsin_sub_self_mem_Icc_two_mul_cube -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arcsine Difference Bounds

**Claim.** For every $x\in[0,1/2]$, the difference $\arcsin(x)-x$ lies in $[0,2x^3]$.

**Proof.** Since $x\in[0,1/2]$, it lies in $[-1,1]$, so $\sin(\arcsin x)=x$; also $\arcsin x\ge0$. The inequality $\sin y\le y$ for $y\ge0$ then gives $x\le\arcsin x$, proving the lower bound. For the upper bound, if $x=0$ the result is immediate. If $x>0$, then $y=\arcsin x>0$. Concavity of sine on $[0,\pi/2]$ gives $(2/\pi)\sin y\le x$ (using $\sin y=x$); since $\pi<4$ and $x\ge0$, this implies $y\le2x$. The cubic estimate $\sin y>y-y^3/4$ for $y>0$ now yields $y-x<y^3/4$. As $0<y\le2x$, we have $y^3/4\le(2x)^3/4=2x^3$. Thus $0\le\arcsin x-x\le2x^3$.
