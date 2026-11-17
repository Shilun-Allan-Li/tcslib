<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_track_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tracked-machine initialization

**Claim.** After one step from its initial configuration, the tracked machine is in the completed tracked configuration of the original machine's initial configuration, with both marker banks marking the origin on every tape.

**Proof.** The tracked machine starts in its special initialization state. Its first transition leaves the input head in place, enters the original machine's initial state, and writes the marker symbol on both marker banks at each tape's current position, which is the origin. The original data tapes remain blank, the work-head positions remain zero, and the output remains empty. These are exactly the fields of the completed tracked initial configuration. For the marker bank whose representation is a tape buffer, the fact that appending the single symbol `true` writes it at the buffer's current end is expressed by the buffer-append identity (`bufferTape_append`); at the origin this agrees with the span marker, since a zero-length span marks exactly the origin (`emCall_span_zero`). The input head is unchanged by a zero movement (`moveInputPos_zero`).

**Key facts.** `Turing.moveInputPos_zero`, `Turing.FinTM.emCall_span_zero`, `Turing.FinTM.bufferTape_append`.
