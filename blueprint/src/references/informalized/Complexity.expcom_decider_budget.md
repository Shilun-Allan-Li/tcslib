<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_decider_budget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential bound for the time budget

**Claim.** For all natural numbers $C,c,d,m$, the stated polynomial and exponential terms together are bounded by $(2C+d+2)2^{(c+d)(m+1)}$.

**Proof.** The elementary estimate $m+1\le2^m$ gives $m+2^m+1\le2^{m+1}$. Set $Q=2^{(c+d)(m+1)}$. For any exponent $e\le c+d$, raising $2^{m+1}$ to $e$ gives a quantity at most $Q$. In particular, $(m+1)^c\le Q$ and $(m+2^m+1)^d\le Q$. Also $1\le Q$. Rewrite the left side as $(2C)(m+1)^c+d(m+2^m+1)^d+2\cdot1$. Applying these three bounds termwise gives at most $(2C+d+2)Q$, as required.
