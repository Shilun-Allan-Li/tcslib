<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_turn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition from the End of Rightward Growth

**Claim.** From the right-growth phase with counter $k$, one simulator step produces the reflected writing-phase configuration, with the source transition's input-head position and output, frontier $z-1$, and right list consisting of the boundary marker followed by the previous right tail.

**Proof.** Write $d$ for the starting simulator configuration and let $A$ be the source transition action at $q$ on the input symbol and scanned work symbols of $c$. The input symbol seen by the simulator, after retraction and interpretation by the sweep input map, is exactly the source input symbol: this follows from the native-input identity (`dg_native`) and the input-position correspondence (`dgInput_read`). The hypothesis on $s$ identifies its stored read symbols with the source machine's scanned symbols. At counter $k$, the right-growth branch of the simulator definition therefore selects the source action $A$, moves the simulator work head left, writes a boundary marker, emits the source output embedded in the enlarged alphabet, and enters the writing phase with all rightward flags initially false. The one-step zipper identity for a leftward move (`sweep_turn_left`) reflects the zipper, decreases the frontier to $z-1$, and places the new boundary marker before the former right tail. The input-position compatibility lemma (`dgPos_move`) identifies the new input position with the source action's updated one, while the output concatenation calculation identifies the emitted output with the embedded output of the successor configuration.

**Key facts.** `Turing.FinTM.dg_native`, `Turing.FinTM.dgInput_read`, `Turing.FinTM.dgPos_move`, `Turing.FinTM.sweep_turn_left`.
