<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.shift_count_lt_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Bound for Natural Numbers

**Claim.** For natural numbers $A$ and $X$ with $1\le X$, one has $(19A+20)X<2^{(A+7)X}$.

**Proof.** First prove by induction on $X$ that $128X\le128^X$. The base case is immediate; at a positive successor, the induction bound and the identity $128^{Y+1}=128^Y\cdot128$ give the result. Next use $A+1\le2^A$ and $2^A\le(2^A)^X$, the latter following from $X\ge1$. Since $19A+20<128(A+1)$, these estimates give
\[(19A+20)X<128(A+1)X=(A+1)(128X)\le (2^A)^X128^X.\]
Finally, the exponent identity $(A+7)X=AX+7X$ shows that $(2^A)^X128^X=2^{(A+7)X}$, proving the inequality.
