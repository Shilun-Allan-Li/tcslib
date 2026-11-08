<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardParams.lean :: Complexity.TQBFHard.configBound_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Count Exponential Bound

**Claim.** With $r=2d(n+1)^c$, $H=3(|S|+1)$, $W=H+3k+1$, and $A=4dW+W+12kd+3k+2|S|+8$, the configuration bound $3(|S|+1)(n+2)3^{k(2r+1)}(2r+1)^k$ is at most $2^{A(n+1)^{c+1}}$.

**Proof.** Set $s=2d(n+1)^c$ and $e=k(2s+1)$. Bound each factor of the configuration count by a power of two: $3(|S|+1)\le 2^{2(|S|+1)}$ (the elementary estimate $\texttt{three_mul_le}$), $n+2\le 2^{n+1}$, and $3^e\le 2^{2e}$, since $3\le 2^2$. Also, $2s+1<2^{2s+1}$, so raising to the $k$th power gives $(2s+1)^k\le 2^e$. Multiplying these estimates bounds the configuration count by $2^{2(|S|+1)+(n+1)+3e}$. It remains to show that this exponent does not exceed $A(n+1)^{c+1}$. Write $P=(n+1)^{c+1}$ and $Q=(n+1)^c$. Since $n+1\ge1$, we have $Q\le P$, $n+1\le P$, and $1\le P$. Substituting $s=2dQ$ into $e=k(2s+1)$ gives $2(|S|+1)+(n+1)+3e=2|S|+3+n+12kdQ+3k$. The definition of $A$ gives $AP=4dWP+WP+12kdP+3kP+2|S|P+8P$. The inequalities $Q\le P$, $n+1\le P$, and $1\le P$, together with $W\ge1$, show that this quantity dominates the preceding exponent. Hence the desired power-of-two bound follows.

**Key facts.** `Complexity.TQBFHard.three_mul_le`.
