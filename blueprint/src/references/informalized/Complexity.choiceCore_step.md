<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.choiceCore_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Choice Simulation

**Claim.** Reading choice bit $u[j]$ advances the core encoding to the encoding of the nondeterministic successor, with an updated valid boundary tag and choice-head position $j+1$.

**Proof.** The encoded choice tape, whose head is at $j$, presents exactly $u[j]$ to the core. Its input work tape presents the simulated configuration's current input symbol, and its remaining work tapes present that configuration's work-tape symbols. Split according to whether the simulated configuration is already halted. If it is halted, the nondeterministic step leaves it unchanged (`Turing.NDTM.stepWith_of_halt`); the core likewise preserves the simulated data, leaves the physical input position fixed (`Turing.moveInputPos_zero`), and advances the choice-head position. The tag remains valid. If the configuration is active, let its transition under bit $u[j]$ be $a$, and let $m$ be the virtualized input movement. The virtual-move correctness fact (`Turing.FinTM.virtualMove_correct`) says both that this movement yields the same logical input-head position as the original move and that the updated tag is valid. The core applies $a$ to the simulated work tapes, advances the choice head, and updates its output-tape representation: the emission-summary identity (`Complexity.captureEmission_correct`) gives the summary of the new output, while the append/update identity for buffered tapes (`Turing.FinTM.bufferTape_append`) gives the updated output tape. Together with the matching input and work-tape data, these coordinate facts establish equality of the successor encodings.

**Key facts.** `Turing.NDTM.stepWith_of_halt`, `Turing.moveInputPos_zero`, `Turing.FinTM.virtualMove_correct`, `Complexity.captureEmission_correct`, `Turing.FinTM.bufferTape_append`, `Turing.FinTM.bufferTape_inputSymbol`.
