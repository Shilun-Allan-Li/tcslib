<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentTM_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Frame properties of the silent embedding

**Claim.** After any number of steps, each tape outside the image of $\iota$ and different from $\mathrm{cap}$ retains its initial contents and head position; the input-head position agrees with $M$'s run, and the output remains $\mathrm{out}_0$.

**Proof.** The run-commutation theorem (`Turing.embedSilentTM_runFrom`) identifies the full embedded run at time $t$ with the silent embedding of $M$'s configuration at that time. For an index $j$ outside the image of $\iota$, the lookup returns no selected slot (`Turing.embedSlot_unselected`); since also $j\ne\mathrm{cap}$, the embedding's fallback branch gives the background contents and head position, namely `tapes j` and `heads j`. The input-head position is copied unchanged by the embedding, while its output component is always `out₀`.

**Key facts.** `Turing.embedSilentTM_runFrom`, `Turing.embedSlot_unselected`.
