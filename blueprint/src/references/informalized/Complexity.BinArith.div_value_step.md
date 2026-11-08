<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.div_value_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step quotient and remainder update

**Claim.** Suppose $c\le1$, $(Qv+\rho)(2P)+(T+cP)=a$, and $\rho<v$. If $v\le c+2\rho$, subtracting $v$ from $c+2\rho$ and increasing the quotient coefficient from $Q$ to $1+2Q$ preserves the represented value and leaves a remainder below $v$. If $v>c+2\rho$, retaining $c+2\rho$ as remainder and using quotient coefficient $2Q$ preserves the value and leaves that remainder below $v$.

**Proof.** Split according to whether $v\le c+2\rho$. In the first case, natural-number subtraction satisfies $(c+2\rho-v)+v=c+2\rho$. Rearranging this identity gives $(1+2Q)v+(c+2\rho-v)=2(Qv+\rho)+c$, so multiplying by $P$, adding $T$, and using the assumed equation yields the claimed equality with $a$. The new remainder is less than $v$ because it is the difference between a quantity at least $v$ and $v$, and the bounds $c\le1$ and $\rho<v$ make that difference strictly smaller than $v$. In the second case, the negation of the comparison gives $c+2\rho<v$. The identity $(2Q)v+(c+2\rho)=2(Qv+\rho)+c$ then gives the required value equation from the hypothesis, and the retained remainder is already below $v$.
