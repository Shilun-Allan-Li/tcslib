<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitRow_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length bound for a visit row

**Claim.** If $t\le N$, the visit row for $x$ and the unary time word of length $t$ has length at most $k(2N+6)$, where $k$ is the number of work tapes.

**Proof.** On the canonical paired request, the exact-row identity expresses the row as the packed list of one visit code for each work tape ($\texttt{Complexity.clVisitRow\_exact}$). Each code has length at most $t+2$, hence at most $N+2$ ($\texttt{Complexity.clVisitCode\_size}$). The packing bound says that if every component has length at most $W$, packing a list of $k$ components has length at most $k(2W+2)$ ($\texttt{Complexity.clFields\_size}$). Apply it with $W=N+2$ to obtain $k(2N+6)$.

**Key facts.** `Complexity.clVisitRow_exact`, `Complexity.clVisitCode_size`, `Complexity.clFields_size`.
