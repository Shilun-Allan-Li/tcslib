<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Visit_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Stored Visit Code

**Claim.** For every $t$ within the producer horizon, the stored visit code for tape $\tau$ in the packed records with cursor $j$ is the optional-time code for the greatest time $s<t$ at which that tape's head occupies its position at time $t$ on the all-zero input of the specified length, or the absent-visit code if no such time exists.

**Proof.** First, the exact-data result identifies the packed record's visit table with the first $T+1$ visit rows, where $T$ is the producer horizon. The visit-row identity then expresses those rows as a generic ordered stream: at time $u$, the entry for tape $\tau$ is the optional-time code of its previous visit. Since $t\le T$, we have $t<T+1$, so the row-indexing result for this stream says that the field at index $tM.k+\tau.val$ is exactly the entry for time $t$ and tape $\tau$. Unfolding the stored visit accessor gives the claimed equality.

**Key facts.** `Complexity.clA5Data_exact`, `Complexity.clA5Visits_rows`, `Complexity.clA5Field_rows`.
