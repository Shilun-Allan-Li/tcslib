<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentTM_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Positions Under Silent Embedding

**Claim.** For every embedded tape index $\iota(i)$, the positions visited through time $t$ by the silently embedded machine are exactly those visited on tape $i$ by $M$. Their numbers of distinct positions are therefore equal.

**Proof.** Let $V$ be the set of positions visited through time $t$ on tape $\iota(i)$ in the embedded run, and let $W$ be the corresponding set on tape $i$ in the run of $M$. The run correspondence theorem states that at every time, the embedded machine's configuration is the silent embedding of the configuration reached by $M$ (\texttt{embedSilentTM\_runFrom}). At tape index $\iota(i)$, the embedding selects precisely slot $i$ (\texttt{embedSlot\_selected}), so the two head positions agree at each time from $0$ through $t$. Thus the sets of these positions, namely $V$ and $W$, are equal. Taking the cardinality of this equality gives the asserted equality of space used.

**Key facts.** `Turing.embedSilentTM_runFrom`, `Turing.embedSlot_selected`.
