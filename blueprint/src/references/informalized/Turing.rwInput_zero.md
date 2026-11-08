<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.rwInput_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewind at the Left Boundary

**Claim.** From input position $0$ in state $\mathrm{rwInput}$, one step enters the anchor state, moves the input head to position $1$, and preserves the tapes, work-head positions, and empty output.

**Proof.** At input position $0$, the scanned input symbol is blank by the definition of the input-head convention. In state $\mathrm{rwInput}$ on a blank, the transition moves right and enters $\mathrm{anchor}$, with no work-tape writes or movements and no output. The right-move formula (`Turing.moveInputPos_pos_of_ne_right`) applies at position $0$ and yields position $1$. Thus the tape contents and work-head positions remain as before, and the output remains empty.

**Key facts.** `Turing.moveInputPos_pos_of_ne_right`.
