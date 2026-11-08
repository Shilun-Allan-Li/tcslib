<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Reach.lean :: Complexity.LogProg.SavitchARM.configBound_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration Count Bound

**Claim.** Under the stated lower bound on $E$, the number of configurations within the specified window is at most $2^{(n+2)^{2E}}$.

**Proof.** Write $s=(n+2)^E$, $Q=|Q|$, and $k$ for the number of work tapes. The hypothesis gives $E\ge1$, so $n+2\le s$. Bound each factor in the configuration count by a power of two: $Q+1\le2^Q$, $n+2\le2^{n+1}$, $3\le2^2$, and $3^{k(2s+1)}\le2^{2k(2s+1)}$, since $3\le2^2$. Also $(2s+1)^k\le2^{k(2s+1)}$, using $m\le2^m$ for natural $m$. Multiplying these estimates bounds the configuration count by $2^{Q+n+3+3k(2s+1)}$. The exponent is at most $(Q+2+9k)s$: use $s\ge n+2$, $s\ge1$, and expand both sides. The hypothesis implies $Q+2+9k\le E\le2^E\le s$, so $(Q+2+9k)s\le s^2$. Therefore the count is at most $2^{s^2}=2^{(n+2)^{2E}}$.
