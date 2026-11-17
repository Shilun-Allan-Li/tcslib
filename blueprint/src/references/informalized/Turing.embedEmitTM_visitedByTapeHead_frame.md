<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitTM_visitedByTapeHead_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unvisited embedded tape stays at its initial head

**Claim.** If tape $j$ is outside the image of the embedding, then through time $t$ it visits only its initial head position, so it uses exactly one cell.

**Proof.** At every time from $0$ through $t$, the run correspondence theorem identifies the embedded configuration with the embedding of the original run (`embedEmitTM_runFrom`). Since $j$ is outside the image, the embedding assigns its head position from the initial heads function (`embedSlot_unselected`); thus its position at every one of these times is $\mathrm{heads}(j)$. The image of the nonempty time range under this constant position function is the singleton $\{\mathrm{heads}(j)\}$. Its cardinality is one, giving the claimed space usage.

**Key facts.** `Turing.embedEmitTM_runFrom`, `Turing.embedSlot_unselected`.
