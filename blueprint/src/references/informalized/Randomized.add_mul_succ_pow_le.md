<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHostsClasses.lean :: Randomized.add_mul_succ_pow_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial power bound

**Claim.** For all natural numbers $A,B,C,n,p$, $A(n+1)^{p+1}+B(n+1)^p+C\le(A+B+C)2^{p+1}(n^{p+1}+1)$.

**Proof.** Since $n+1\ge1$, increasing the exponent from $p$ to $p+1$ gives $(n+1)^p\le(n+1)^{p+1}$, and $(n+1)^{p+1}\ge1$. Multiplying these inequalities by $B$ and $C$, respectively, shows that the left side is at most $(A+B+C)(n+1)^{p+1}$. The bound $(n+1)^q\le2^q(n^q+1)$ (`succ_pow_le_two_pow_mul`), applied with $q=p+1$, then gives the desired upper bound. Associativity and commutativity of multiplication put it in the displayed form.

**Key facts.** `Randomized.succ_pow_le_two_pow_mul`.
