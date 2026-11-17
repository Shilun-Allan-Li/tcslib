<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.rwTape_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rewinding Across a Stored Work Symbol

**Claim.** If the first work-tape head is at $j$ with $0\le j<|x|$ while the machine is in state $\mathrm{rwTape}$, one step keeps that state and the input position, moves the first work-tape head to $j-1$, and leaves all other data unchanged.

**Proof.** At position $j$, the first work tape contains $x[j]$, which is present because $j<|x|$. Thus the transition in state $\mathrm{rwTape}$ sees a nonblank symbol and moves the first work-tape head left by one while staying in $\mathrm{rwTape}$; it makes no writes, leaves every other work-tape head stationary, and emits nothing. The input head is stationary by `Turing.moveInputPos_zero`. Applying the action changes the first head position from $j$ to $j-1$ and preserves the tape contents and output.

**Key facts.** `Turing.moveInputPos_zero`.
