<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecTransitionCNF_cost_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Transition Formula Cost

**Claim.** When the coefficient $|\mathrm{State}(M)|+6k+5$ is at most $C$, the transition CNF cost is at most $2^k$ times the number of transition cases, times $2^{3k+7}(3k+8)$, times $C(s+n+2)^{k+2}$.

**Proof.** Apply the transition-formula cost bound, which reduces the claim to bounding the numbers of position choices and encoded bits. There are at most $2^k(s+n+2)^{k+1}$ position choices (\texttt{Complexity.codecPositions_card_le}). The bit-count bound gives at most $C(s+n+1)$ bits under the coefficient hypothesis (\texttt{Complexity.codecBit_card_le}); since $s+n+1\le s+n+2$, this is at most $C(s+n+2)$. Substitute both estimates into the transition-formula bound (\texttt{Complexity.codecTransitionCNF_cost}). Collecting factors yields $2^k$ times the number of transition cases, times the per-gate factor $2^{3k+7}(3k+8)$, times $C(s+n+2)^{k+2}$, as claimed.

**Key facts.** `Complexity.codecPositions_card_le`, `Complexity.codecBit_card_le`, `Complexity.codecTransitionCNF_cost`.
