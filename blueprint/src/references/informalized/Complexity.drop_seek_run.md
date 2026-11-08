<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_seek_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Seek Procedure Run

**Claim.** Under the stated register bounds and relations, the seek procedure reaches the hit state with the stated pointer and index updates if the query index lies within the searched range. Otherwise it reaches the false-answer state in suffix mode or the stage that clears the pointer in ordinary mode, with the stated updates. The invariant holds throughout the run.

**Proof.** The indexed-seek loop theorem (`Complexity.LogProg.indexedSeek_loop`) applies to this machine with pointer register $0$, the mode-dependent limit register $2$ or $5$, index register $7$, and query register $6$. The distinctness conditions among the registers hold for either choice of suffix mode; the stride is $2$ in suffix mode and $4$ otherwise. The specified seek, probe, bump, and walk states implement the theorem's comparisons and increments, while the hypotheses give the initial limit relation, the register bounds, and the index ordering needed for the loop. If register $6$ lies in the searched interval, the loop stops on the matching index and advances the pointer by one stride for each index traversed, giving the stated difference-based update and setting register $7$ to register $6$. If it lies beyond the interval, the loop reaches its miss endpoint, with the appropriate mode-dependent state and the endpoint register values stated. The loop theorem also carries the safety invariant through every preceding configuration.

**Key facts.** `Complexity.LogProg.indexedSeek_loop`.
