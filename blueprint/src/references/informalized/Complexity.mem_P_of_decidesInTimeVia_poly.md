<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/ModelInvariance.lean :: Complexity.mem_P_of_decidesInTimeVia_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time over an Encoded Alphabet

**Claim.** If a finite-state machine over a finite encoded alphabet decides a binary language on symbolwise encoded inputs within the stated polynomial time bound, then the binary language belongs to $\mathsf{P}$.

**Proof.** The machine's encoded-alphabet decision procedure yields membership in deterministic time with bound $C(n+1)^d+1$ (`Complexity.mem_DTIME_of_decidesInTimeVia`). To compare this with the defining polynomial bound for $\mathsf{P}$, note that $(n+1)^d$ is positive, so $C(n+1)^d+1\le (C+1)(n+1)^d$. The elementary estimate $(n+1)^d\le 2^d(n^d+1)$ (`Complexity.succ_pow_le`) therefore gives $C(n+1)^d+1\le (C+1)2^d(n^d+1)$. The polynomial-time criterion for a pointwise bounded deterministic-time class (`Complexity.mem_P_of_dtime_le`) now implies that the language is in $\mathsf{P}$.

**Key facts.** `Complexity.mem_DTIME_of_decidesInTimeVia`, `Complexity.succ_pow_le`, `Complexity.mem_P_of_dtime_le`.
