<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_ledger_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Ledger Bound

**Claim.** For any fixed natural parameters $C,c,c_V,e,c_I,c_P,K$, the displayed ledger expression is bounded by a constant times a fixed power of $n+1$.

**Proof.** Choose exponent $f=(c+1)(e+1)$ and constant $A=(C+1)+c_V((C+1)^e+1)+c_I+c_P+1$. We show the expression is at most $K(2A+1)(n+1)^f$.

Put $R=(n+1)^f$. Since $f\ge c+1$ and $f\ge(c+1)e$, powers of $n+1$ with either of these smaller exponents are at most $R$. Also $1\le R$ and $n+1\le R$. First, $n+C(n+1)^c\le(C+1)(n+1)^{c+1}\le(C+1)R$: the first inequality follows by bounding both $n$ and $(n+1)^c$ by $(n+1)^{c+1}$. Raising this bound to the $e$th power gives $(n+C(n+1)^c)^e\le(C+1)^eR$, using $(n+1)^{(c+1)e}\le R$. Since $1\le R$, it follows that $c_V((n+C(n+1)^c)^e+1)\le c_V((C+1)^e+1)R$. The remaining terms satisfy $c_I\le c_IR$, $c_P(n+1)\le c_PR$, and $1\le R$. Adding these estimates bounds the full inner ledger quantity by $AR$. Finally, $2AR+R=(2A+1)R$, giving the claimed bound after multiplication by $K$.
