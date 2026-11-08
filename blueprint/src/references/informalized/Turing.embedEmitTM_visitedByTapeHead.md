<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitTM_visitedByTapeHead -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited positions under tape embedding

**Claim.** For every time $t$ and original tape index $i$, the embedded simulation visits exactly the positions visited by tape $i$ of the original machine; the two tapes therefore use the same number of distinct positions.

**Proof.** First compare the visited-position sets. By definition, each is the image of the times from $0$ through $t$ under the corresponding head-position function. The run correspondence theorem says that, at every such time, the embedded machine's configuration is the embedding of the original run (`embedEmitTM_runFrom`). At the selected tape index $\iota(i)$, the embedding selects exactly tape $i$ (`embedSlot_selected`), so these two head-position functions agree pointwise. Their images, and hence their visited-position sets, are equal. Taking the cardinality of this equality gives the equality of space used.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.embedSlot_selected`.
