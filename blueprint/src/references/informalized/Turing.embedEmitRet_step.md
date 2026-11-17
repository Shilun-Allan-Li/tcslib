<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedEmitRet_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Return-State Simulation

**Claim.** From a nonhalted configuration, one step of the return-state simulation on the embedded configuration equals the embedded next configuration, with its state represented in the left summand if active and in the distinguished right-summand state if halted.

**Proof.** The general step-compatibility result `Turing.embedReturn_step` applies to a machine whose left-summand transitions are the return-state encoding of another machine's transitions, and whose right-summand transitions idle in the distinguished state. The return-state machine has these transition rules by definition. Rewriting the embedded configuration's state using `Turing.embedReturnCfg_live` is valid because the original configuration is not halted. The remaining step is identified with the embedded machine's step by `Turing.embedEmit_step`. Combining these facts gives the asserted one-step equality.

**Key facts.** `Turing.embedReturn_step`, `Turing.embedReturnCfg_live`, `Turing.embedEmit_step`.
