<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.inputSymbol_take_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol Under Truncation

**Claim.** If two configurations have the same input-head position, and the position in the configuration on $x$ is at most $m$, then they read the same symbol, with the second configuration reading the prefix of $x$ of length at most $m$.

**Proof.** Let $p$ be the common head position. If $p=0$, both configurations read no symbol. If $p=|x|+1$, the head in the first configuration is at the right boundary; the bound $p\le m$ forces the truncated input to have length at most $p-1$, so the second head is at its right boundary as well. Both configurations again read no symbol. In the remaining case, the head is strictly between the two boundary positions. Set $j=p-1$. The interior-position formula for the symbol read (`Turing.inputSymbolInner`) says that the first configuration reads the $j$th symbol of $x$ and the second reads the $j$th symbol of $x.take m$. Since $j<m$, taking this prefix preserves the symbol at position $j$ (`List.getElem_take`), so the read symbols agree.

**Key facts.** `Turing.inputSymbolInner`.
