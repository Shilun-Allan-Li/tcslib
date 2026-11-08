<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.log_poly_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic bound for a polynomial expression

**Claim.** For fixed nonnegative integers $A,c,B$, there is a constant $K$ such that for every nonnegative integer $n$, the base-two logarithm of $A(n+1)^c+B$, rounded down and increased by one, is at most $K$ times the base-two logarithm of $n$, rounded down and increased by one.

**Proof.** Choose $K=A+B+c+2$, and write $L=\lfloor\log_2 n\rfloor$. The bound $n+1\le 2^{L+1}$ implies $(n+1)^c\le 2^{c(L+1)}$. Also $A<2^A$ and $B<2^B$. Consequently the term $A(n+1)^c$ is at most $2^{A+c(L+1)}$, and $B$ is at most the same larger power after increasing the exponent to $A+B+c(L+1)$. Their sum is strictly below $2^{A+B+c(L+1)+1}$. The defining growth property of the base-two logarithm therefore gives $\lfloor\log_2(A(n+1)^c+B)\rfloor < A+B+c(L+1)+1$ (with the zero case handled directly). Finally, since $L+1\ge1$, the constant part $A+B+2$ is at most $(A+B+2)(L+1)$. Adding the remaining $c(L+1)$ term yields the claimed bound with the chosen $K$.

**Key facts.** `Complexity.LogProg.succ_le_two_pow_log`.
