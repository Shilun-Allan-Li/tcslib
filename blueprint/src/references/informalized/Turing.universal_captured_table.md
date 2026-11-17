<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_captured_table -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Capturing the Canonical Transition Table

**Claim.** The capture machine reaches the interpreter's initial state within the stated time bound, with the input head at the specified position, the captured table tape holding the buffer-tape encoding of the canonical serialization, and empty output.

**Proof.** The canonizer-completion result gives a halted canonizer configuration at time $3|\alpha|+4+T_c(|\alpha|)$, with the canonical serialization as output and the input head at position $2|\alpha|+3$ (`universalCanon_complete`). The capture-start property transfers this halted configuration to the capture machine: within one further step it reaches the captured configuration corresponding to that completed canonizer run (`universalCapture_start`). Thus the capture time is at most $3|\alpha|+5+T_c(|\alpha|)$. In that captured configuration, the interpreter state and input position are the asserted ones, and the output is empty. The tape-block identity says that the middle tape of the block layout is the captured buffer (`tapeBlocks_buffer`); using the canonizer's output equality, this middle tape is the buffer-tape encoding of the canonical serialization. These component equalities give all the claims.

**Key facts.** `Turing.universalCanon_complete`, `Turing.universalCapture_start`, `Turing.FinTM.tapeBlocks_buffer`.
