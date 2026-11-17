<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.mapPayload_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of Payload Replay

**Claim.** Starting in the payload-replay state with capture-head displacement $0$ and output $o$, after $|c.output|+1$ steps the controller is halted and the output is $o$ followed by $c.output$.

**Proof.** Apply the replay description `mapPayload_replay` with $j=|c.output|$. It identifies the configuration after these first $|c.output|$ steps: the controller is still in the payload-replay state, the capture head has displacement $|c.output|$, and the output is $o\mathbin{++}c.output.take(|c.output|)=o\mathbin{++}c.output$. One further step is described by `runFrom_succ_eq_step'`: it is the machine's next transition from that configuration. In the payload-replay state, the capture tape has no symbol at this position, so the transition halts without writing an output symbol. Unfolding the transition and configuration definitions confirms that the state is now none and the output remains $o\mathbin{++}c.output$.

**Key facts.** `Turing.FinTM.mapPayload_replay`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
