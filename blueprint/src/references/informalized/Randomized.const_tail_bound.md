<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.const_tail_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Tail Bound

**Claim.** For all natural numbers $b,e,n$, with $P(a,k,n)=a(n+1)^k$, the stated exponential tail is at most $(1/2)^{P(b,e,n)}$.

**Proof.** Set $x=4(1/6)^2$. Direct rational arithmetic gives $0\le x\le1$ and $9x\ge1$. The exponent on the left is large enough for the exponential estimate: since $(n+1)^e\ge1$ and $P(18b+18,e,n)/2=(9b+9)(n+1)^e$, we have
\[
9\bigl(P(b,e,n)+1\bigr)=9\bigl(b(n+1)^e+1\bigr)\le (9b+9)(n+1)^e.
\]
Apply the bound that $(1-x)^q\le(1/2)^T$ whenever $mx\ge1$ and $mT\le q$ (Randomized.one_sub_pow_le_half_pow), taking $m=9$, $T=P(b,e,n)+1$, and $q=P(18b+18,e,n)/2$. Multiplication by $2$ preserves the inequality. Finally, $2(1/2)^{P(b,e,n)+1}=(1/2)^{P(b,e,n)}$, giving the claim.

**Key facts.** `Randomized.one_sub_pow_le_half_pow`.
