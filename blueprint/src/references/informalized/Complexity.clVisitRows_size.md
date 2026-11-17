<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clVisitRows_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visit table length bound

**Claim.** For every $t\le N$, the table of the first $t$ visit rows has length at most $t\,k(2N+6)$.

**Proof.** Induct on $t$, proving the bound for every $t\le N$. At $t=0$ the table is empty. For the successor case, the table is the previous table followed by the row at time $t$. The induction hypothesis bounds the previous table by $t\,k(2N+6)$, and the visit-row length bound applies because $t\le N$ ($\texttt{Complexity.clVisitRow\_size}$). Adding these estimates gives $(t+1)k(2N+6)$, as required.

**Key facts.** `Complexity.clVisitRow_size`.
