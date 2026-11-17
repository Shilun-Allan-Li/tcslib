<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopBuffer_write -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the First Buffer Symbol

**Claim.** Changing the buffer for $\mathrm{pre}\,\mathrm{old}\,\mathrm{bs}$ at cell $|\mathrm{pre}|$ to contain $\mathrm{new}$ gives the buffer for $\mathrm{pre}\,\mathrm{new}\,\mathrm{bs}$.

**Proof.** Compare the two tape functions at an arbitrary integer cell $z$. At the updated cell $z=|\mathrm{pre}|$, the update assigns exactly the symbol that distinguishes the two lists, so both tapes agree there. At any other cell the update leaves the original tape unchanged. For negative $z$, both buffers contain no symbol. For nonnegative $z$, if its natural index lies before $|\mathrm{pre}|$, both lists read the same position in the common prefix. If it lies after that boundary, both lists read the corresponding position in the common suffix; the list-index calculation excludes the differing first symbol of the suffix precisely because the index is strictly past it. Thus the two tape functions agree at every cell.
