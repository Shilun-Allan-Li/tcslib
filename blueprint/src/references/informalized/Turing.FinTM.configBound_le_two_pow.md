<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/WindowClock.lean :: Turing.FinTM.configBound_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration bound by a power of two

**Claim.** For a finite Boolean-alphabet Turing machine with state set $Q$ and $k$ work tapes, the configuration bound $(|Q|+1)(n+2)3^{k(2s+1)}(2s+1)^k$ is at most $2^{|Q|+w(n)+3k(2s+1)}$, where $w(n)$ is the length of the binary expansion of $n+1$.

**Proof.** Bound each factor of the configuration count by a power of two. First, $|Q|+1\le 2^{|Q|}$, using the standard bound $m+1\le 2^m$. By the binary-size bound for $n+1$, we have $n+2\le 2^{w(n)}$. Put $a=k(2s+1)$. Since $3\le 4$, $3^a\le 4^a=2^{2a}$. Also, $2s+1\le 2^k$ is not needed: the elementary inequality $m\le 2^m$ gives $(2s+1)^k\le 2^{k(2s+1)}$. Multiplying these four bounds gives the desired product of powers of two. Combining their exponents yields $|Q|+w(n)+2a+a=|Q|+w(n)+3k(2s+1)$.
