<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_output_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output-Phase Step

**Claim.** Under the stated transition hypothesis, one step from the lifted configuration in control $q$, with buffer head at $p$ and output $o$, reaches the lifted configuration in control $q'$, with buffer head at $p+d$ and output $o$ followed by $e$ when present.

**Proof.** The lifted configuration reads at lane $5$ the buffer symbol at position $p$, by the definitions of the lift and the buffer tape. Apply the transition hypothesis to this input symbol and the tuple of work-tape symbols: the transition is the specified administrative action. Its input-head movement is zero, so the input position is unchanged (the zero-movement identity is `moveInputPos_zero`). Its work-tape actions leave lanes $0$ through $4$ unchanged and move lane $5$ by $d$. Thus the four original tapes and the clock lane remain as in the lift, while the buffer head moves from $p$ to $p+d$. Finally, the action enters $q'$ and appends the optional emission to the output, giving $o$ followed by $e$ when $e$ is present.

**Key facts.** `Turing.moveInputPos_zero`.
