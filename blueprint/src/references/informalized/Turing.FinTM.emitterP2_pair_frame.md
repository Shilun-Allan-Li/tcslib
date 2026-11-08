<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_pair_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Comparator Configuration

**Claim.** Embedding the comparator configuration into the two designated host slots, with the prescribed background on all other tapes, and mapping its state by $e$, gives the canonical host configuration with candidate $s$ and the designated words $u$ and $v$.

**Proof.** Use the framed configuration embedding with the two-slot index map. The selected-slot conditions follow by checking the two possible source slots: the first receives the comparator's first tape and the second its second tape, with both head positions at zero. For an unselected host slot, decompose its index into the candidate slot or one of the two banks. In the banks, an unselected position is not the designated first position, so its state word is empty; the candidate slot carries $s$. Empty words yield blank tapes by the fact that the tape encoding of the empty word is blank everywhere (Turing.FinTM.bufferTape_nil). Hence the ambient contents and zero heads match the target on every unselected slot. The remaining configuration fields agree directly, and the framing result completes the proof.

**Key facts.** `Turing.FinTM.bufferTape_nil`, `Turing.FinTM.emitterP2_frame`.
