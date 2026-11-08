<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.rwTape_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding at a Blank Work Cell

**Claim.** When the first work-tape head is at position $-1$ in state $\mathrm{rwTape}$, with the input head at the right boundary blank cell, one step enters $\mathrm{rwInput0}$ and moves the first work-tape head to $0$, preserving the other configuration data.

**Proof.** The first work-tape head scans a blank: its position is $-1$, and the stored word is buffered only at nonnegative cells. In state $\mathrm{rwTape}$ on a blank, the machine’s transition keeps the input head fixed, moves the first work-tape head right by one, and enters $\mathrm{rwInput0}$; all other work-tape actions are stationary, and there is no write or output. The stationary input-head fact (`Turing.moveInputPos_zero`) preserves the right-boundary position. Applying the action adds one to the first head position, taking $-1$ to $0$, and leaves all tape contents, other head positions, and output unchanged.

**Key facts.** `Turing.moveInputPos_zero`.
