<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_rewind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input rewind phase

**Claim.** From any configuration of the three-state rewind machine in state $0$, the round body reaches state $2$ at input-head position $1$ within the current input-head position plus $2$ steps, preserving every other configuration component and the rewind-phase label throughout; the run avoids the anchor state through that time.

**Proof.** The three-state rewind machine first moves left into state $1$, then continues moving left while it reads input symbols. When it reaches the blank position, it moves right into state $2$. The catalogued rewind property (`catalogRewind`) gives a time bounded by the starting input-head position plus $2$ at which the machine has state $2$ and input-head position $1`; since its actions do not alter work tapes, work-head positions, or output, these components remain as in the starting configuration. Embed the three-state machine into the round body's rewind states with the fixed Boolean label $ok$. The host transitions agree with the embedded rewind transitions before state $2$, the embedding avoids the anchor state, and the source machine fixes configurations in state $2$. The embedding-and-cut result (`splitEmbed_cut`) therefore transfers the run to the round body, yielding the claimed endpoint and anchor avoidance. At that stopping state the host's zero-movement action fixes the configuration, using the fact that zero movement preserves the input-head position (`moveInputPos_zero`) and the control-action description (`controlAction_apply`).

**Key facts.** `Turing.FinTM.catalogRewind`, `Turing.FinTM.splitEmbed_cut`, `Turing.FinTM.controlAction_apply`, `Turing.moveInputPos_zero`.
