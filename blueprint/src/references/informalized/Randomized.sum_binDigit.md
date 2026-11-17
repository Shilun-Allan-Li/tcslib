<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.sum_binDigit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite sum of binary digits

**Claim.** For $\rho<1$ and natural number $K$, the first $K$ binary digits of $\rho$, weighted by $2^{-(i+1)}$, sum to $\lfloor2^K\rho\rfloor/2^K$.

**Proof.** Induct on $K$. At $K=0$, the sum is empty and the right side is zero because $\rho<1$ implies its natural floor is zero. For the step, the induction hypothesis accounts for the first $K$ digits. Let $N=\lfloor2^{K+1}\rho\rfloor$. Dividing this floor by $2$ gives $\lfloor2^K\rho\rfloor$, by the floor identity for division by a natural number. Euclidean division therefore writes $N=2\lfloor2^K\rho\rfloor+(N\bmod2)$. The remainder is either $0$ or $1$, and is exactly the next binary digit, as defined by the parity of $N$. Substituting this decomposition into the target expression shows that the new term contributes $(N\bmod2)/2^{K+1}$, which is precisely the next weighted digit. This completes the induction.
