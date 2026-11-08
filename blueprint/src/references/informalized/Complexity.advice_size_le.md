<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PAdviceSubsetPPoly.lean :: Complexity.advice_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Advice-Size Polynomial Bound

**Claim.** For all natural numbers $k,K,c,c_0,C,d,n$, the stated advice-size expression is bounded by the displayed constant multiple of $(n+1)^{2(c+d+1)}$.

**Proof.** Set $R=(n+1)^{c+d+1}$. Since $n+1\ge1$ and $c+d+1$ is at least each of $c$ and $d$, we have $1\le R$, $n+1\le R$, $n^c\le R$, and $(n+1)^d\le R$. Also $R\le R^2$. Thus the exponent on the right-hand side of the claimed inequality gives exactly $R^2$. First, $c_0(n^c+1)\le 2c_0R$, so $c_0(n^c+1)+1\le(2c_0+1)R$. Second, bounding each term in the other factor by the estimates above gives
\[
k\bigl(2c_0(n^c+1)+1\bigr)+(2n+2+C(n+1)^d)+3
\le \bigl(k(4c_0+1)+C+7\bigr)R.
\]
Multiplying these bounds and then multiplying by $K$ bounds the product term by $(2c_0+1)(k(4c_0+1)+C+7)K R^2$. The remaining term satisfies $n+C(n+1)^d+2\le(C+3)R^2$. Adding the two bounds yields the stated inequality.
