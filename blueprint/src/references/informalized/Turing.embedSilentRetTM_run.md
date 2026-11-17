<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSilentRetTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run of the silent return machine

**Claim.** Under the stated hypotheses, before time $T$ the return machine agrees with the embedded run of $M$ in its left-summand states; at time $T$ it has the embedded halted configuration with the return state, and it has not entered that return state earlier.

**Proof.** Apply the through-halt theorem (`Turing.embedThroughHalt`) with the silent configuration embedding as the configuration map. Its hypotheses are supplied as follows: the embedding preserves the state, since its state component is unchanged; and the required one-step correspondence is `Turing.embedSilentRet_step`. The initial state is present by $hc$, the run stays live before $T$ by $hlive$, and it is halted at $T$ by $hhalt$. The theorem then gives the claimed agreement at each earlier time, the specified return-state configuration at time $T$, and the fact that the return state does not occur earlier.

**Key facts.** `Turing.embedSilentRet_step`, `Turing.embedThroughHalt`.
