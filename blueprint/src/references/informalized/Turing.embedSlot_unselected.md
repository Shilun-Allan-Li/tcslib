<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSlot_unselected -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unembedded Tape Index Has No Selected Slot

**Claim.** If $j$ lies outside the image of $\iota$, then no slot is selected at $j$.

**Proof.** A slot would be selected only if some index $i$ satisfied $\iota(i)=j$. Such an equality would put $j$ in the image of $\iota$, contrary to the hypothesis. Therefore the search finds no slot.
