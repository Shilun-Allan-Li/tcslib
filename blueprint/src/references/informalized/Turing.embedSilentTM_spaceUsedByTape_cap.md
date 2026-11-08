<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentTM_spaceUsedByTape_cap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space bound for the output tape

**Claim.** The number of distinct head positions visited on the distinguished tape through time $t$ is at most the output length at time $t$ minus the initial output length, plus one.

**Proof.** Let $V$ be the set of head positions visited on tape $\mathrm{cap}$ through time $t$. By definition it is the image of the times $u\le t$ under the head-position function. At each such time, run commutation (`Turing.embedSilentTM_runFrom`) identifies the embedded configuration with the embedding of $M$'s configuration at time $u$. The distinguished tape is outside the image of $\iota$, so its slot is unselected (`Turing.embedSlot_unselected`); in the embedding its head is therefore at the integer position $|\mathrm{pre}|+|\mathrm{output}_u|$. The output-prefix theorem (`Turing.MultiTapeTM.output_prefix`) implies that output lengths are nondecreasing, so every such position lies in the integer interval from $|\mathrm{pre}|+|c.output|$ through $|\mathrm{pre}|+|	ext{output}_t|$. Hence $V$ is contained in this interval. Its cardinality is at most the interval's cardinality, which for integer endpoints is the endpoint difference plus one, namely $|	ext{output}_t|-|c.output|+1$.

**Key facts.** `Turing.MultiTapeTM.output_prefix`, `Turing.embedSilentTM_runFrom`, `Turing.embedSlot_unselected`.
