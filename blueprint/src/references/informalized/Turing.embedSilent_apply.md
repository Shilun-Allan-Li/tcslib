<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilent_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Action Commutes with Silent Configuration Embedding

**Claim.** Applying the embedded version of an action $a$ to the silent embedding of a configuration $c$ yields the silent embedding of the configuration obtained by applying $a$ to $c$.

**Proof.** Compare the two configurations component by component. Their states and input-head positions agree directly, and their outputs agree because the embedded action suppresses output while the emitted symbol is instead written on the distinguished tape. For the tape contents and head positions, fix an index $j$. If $j=\iota(i)$ for a slot $i$, the embedding uses the original tape action and original tape data, so applying the action agrees with first applying $a$ and then embedding. If $j$ is not an embedded slot and $j=\mathrm{cap}$, an output symbol, when present, is written at the end of the buffered word $\mathrm{pre}\mathbin{++}c.\mathrm{output}$, while the cap head advances by one; this is exactly the effect of appending that symbol to the buffered word (\texttt{FinTM.bufferTape\_append}). With no output symbol, both the buffer and cap head remain unchanged. At any other unmapped tape, the embedded action leaves its contents and head position fixed, matching the definition of the silent embedding after applying $a$. These cases establish equality of the configurations.

**Key facts.** `Turing.FinTM.bufferTape_append`.
