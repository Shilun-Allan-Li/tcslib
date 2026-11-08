<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentTM_visitedByTapeHead_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed Head on an Unmapped Tape

**Claim.** If tape index $j$ lies outside the image of $\iota$ and differs from $\mathrm{cap}$, then through time $t$ the embedded computation visits exactly the singleton containing $\mathrm{heads}(j)$, and uses exactly one cell on that tape.

**Proof.** The run correspondence theorem identifies the embedded configuration at each time with the silent embedding of the corresponding configuration of $M$ (\texttt{embedSilentTM\_runFrom}). Since $j$ is outside the image of $\iota$, its selected slot is empty (\texttt{embedSlot\_unselected}); and since $j\ne\mathrm{cap}$, the embedding assigns it head position $\mathrm{heads}(j)$. Consequently this head position is constant at every time from $0$ through $t$, so the set of visited positions is the singleton $\{\mathrm{heads}(j)\}$. A singleton has cardinality one, which gives the space assertion.

**Key facts.** `Turing.embedSilentTM_runFrom`, `Turing.embedSlot_unselected`.
