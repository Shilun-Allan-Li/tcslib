<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/Classes.lean :: Complexity.b1_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Budget Bound

**Claim.** For all natural numbers $a,c,k,C,d,n$, the stated product of the polynomial budget terms is bounded by $a(1+C)(2c+1)^{d+2}2^{k(d+2)}(n^{k(d+2)}+1)$.

**Proof.** Set $Y=c(n^k+1)+1$. The polynomial estimate bounds $Y$ by $(2c+1)(n+1)^k$ (\texttt{Complexity.b1_poly_succ_le}), and $Y\ge1$. Hence $Y\le Y^{d+1}$ and $CY^d\le CY^{d+1}$, so $Y+CY^d\le(1+C)Y^{d+1}$. Multiplying by $aY$ bounds the left side by $a(1+C)Y^{d+2}$. Raising the estimate for $Y$ to the power $d+2$ gives $Y^{d+2}\le(2c+1)^{d+2}(n+1)^{k(d+2)}$. Finally, apply $(n+1)^e\le2^e(n^e+1)$ with $e=k(d+2)$ (\texttt{Complexity.succ_pow_le}) and rearrange the factors. This is the desired bound.

**Key facts.** `Complexity.b1_poly_succ_le`, `Complexity.succ_pow_le`.
