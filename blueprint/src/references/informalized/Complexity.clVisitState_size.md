<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitState_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on retained-state length

**Claim.** If $|x|\le L$ and $N\le L$, then every state after $j\le N$ producer steps from the encoded initial state has length at most $(8+8k)(L+1)^2$.

**Proof.** Use the producer-step orbit identity to write the state after $j$ iterations as the encoding of $x$, the unary word for time $j$, and the table of its first $j$ rows ($\texttt{Complexity.clVisitStep\_orbit}$). The table-length bound gives at most $j\,k(2N+6)$ bits ($\texttt{Complexity.clVisitRows\_size}$). Since $j\le N\le L$ and $|x|\le L$, the two header components and this table together have length at most $2L+2L+4+Lk(2L+6)$. Expanding the proposed bound shows this quantity is at most $(8+8k)(L+1)^2$.

**Key facts.** `Complexity.clVisitStep_orbit`, `Complexity.clVisitRows_size`.
