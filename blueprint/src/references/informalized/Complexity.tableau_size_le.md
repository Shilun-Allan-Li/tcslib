<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPoly.lean :: Complexity.tableau_size_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tableau Size Bound

**Claim.** For all natural numbers $W,c,C,d,n$, the stated tableau-size expression is bounded above by $(2+W+c(C+2)^2W)(n+1)^{2(d+1)}$.

**Proof.** Set $P=(n+1)^{d+1}$. Since $n+1
e0$, we have $1\le P$, and since $d+1
e0$, also $n+1\le P$. These bounds imply $(C+1)P+1\le(C+2)P$, hence after squaring, $((C+1)P+1)^2\le(C+2)^2P^2$. Also $P\le P^2$, so multiplying the first inequality by $c$ and adding $1\le P^2$ yields $c((C+1)P+1)^2+1\le(c(C+2)^2+1)P^2$. Multiplication by $W$ preserves the inequality. Finally, $(n+1)^{2(d+1)}=P^2$, and the remaining additive terms $n+2$ are absorbed by $2P^2$ using $n+1\le P$ and $1\le P$. Rearranging gives the claimed bound.
