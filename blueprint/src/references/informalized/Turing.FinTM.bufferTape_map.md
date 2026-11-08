<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.FinTM.bufferTape_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a buffer tape

**Claim.** The buffer tape for the letterwise $e$-image of $w$ at cell $p$ equals the value on the buffer tape for $w$ at $p$, mapped through $e$.

**Proof.** If $p$ is negative, both buffer tapes are blank by definition. If $p$ is nonnegative, the tape values are the optional list entries at the natural index corresponding to $p$. Mapping a list through $e$ maps each present entry to its image and keeps an absent entry absent. Thus the two optional symbols agree.
