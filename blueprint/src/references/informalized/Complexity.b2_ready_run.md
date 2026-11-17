<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.b2_ready_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Assembly Rewind

**Claim.** For any choice word of length $j+1$, the host run from the assembly-rewind configuration at cell $j-1$ ends in the verifier phase initialized on $y$, with true boundary tag and the scheduler data inherited from $c$.

**Proof.** Proceed by induction on $j$, generalizing the choice word. If $j=0$, its length is one, so it consists of a single bit. The one-step completion fact (`Complexity.b2_ready_done`) says that this step sends the rewind configuration at position $-1$ directly to the desired verifier configuration. If $j>0$, write the choice word as a first bit followed by a tail. The host run on this word is the run on the tail after taking the first step (`Turing.NDTM.runWith_cons`). Since $j>0$, that first step is the ordinary leftward rewind step (`Complexity.b2_ready_step`): it moves the assembly head from $j-1$ to the preceding cell, which is the position required for the induction hypothesis with index $j-1$. The tail has length $j$, so the induction hypothesis completes the run to the stated verifier configuration.

**Key facts.** `Complexity.b2_ready_done`, `Complexity.b2_ready_step`, `Turing.NDTM.runWith_cons`.
