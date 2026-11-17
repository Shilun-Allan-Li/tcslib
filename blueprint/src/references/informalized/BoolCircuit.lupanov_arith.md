<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Lupanov.lean :: BoolCircuit.lupanov_arith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Arithmetic bound for circuit size

**Claim.** For every natural number $n$, the displayed expression involving $n$, its base-two logarithm, and powers of two is at most $40\cdot2^n$.

**Proof.** Put $L=\lfloor\log_2 n\rfloor$, $k=L-1$, $s=2^k$, and $M=2^{n-k}$. The proof uses $Ms=2^n$. The logarithm bounds give $n+1\le4s$ and $s\le n+1$. They also give $s2^s\le2\cdot2^n$: when $L>0$, use $2^L=2s\le n$ and $s\le2^s$ to obtain $s2^s\le2^{2s}\le2^n$; the $L=0$ case follows directly from $s=1$. The remaining estimate $(n+1)^2\le4\cdot2^n$ is the square-versus-power bound (`BoolCircuit.succ_sq_le_four_mul_two_pow`). Now bound the four summands after multiplying by $n+1$: the $2n$ term is at most $2(n+1)^2\le8\cdot2^n$; the $4M$ term is at most $4(4s)M=16\cdot2^n$; the $2s$ term is at most $2(n+1)^2\le8\cdot2^n$; and the $2^s$ term is at most $4s2^s\le8\cdot2^n$. Their bounds sum to $40\cdot2^n$.

**Key facts.** `BoolCircuit.succ_sq_le_four_mul_two_pow`.
