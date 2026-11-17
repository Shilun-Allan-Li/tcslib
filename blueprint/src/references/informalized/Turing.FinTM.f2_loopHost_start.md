<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopHost_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Host Startup

**Claim.** If the body’s run from its initial configuration first reaches the anchor configuration with tape word $s$ at time $t$, then the ready host reaches the corresponding call configuration after exactly $t+2$ steps.

**Proof.** The ready configuration is the startup call on the body’s initial configuration, with the fuel word taken from the output of the fuel configuration (`f2_loopReady_call`). The anchor-return lemma applies to the body run through time $t$: its endpoint is at the anchor, and the guard ensures there was no earlier visit. It therefore places the host, after $t+1$ steps, in the startup call carrying the body’s endpoint configuration halted and the false flag (`f2_loopHost_anchor_return`). One more step performs the release transition, changing startup to false, setting the body state to the anchor, enabling release, and clearing the flag (`f2_loopHost_release`). Since the endpoint configuration is exactly the stipulated anchor configuration with tape word $s$, this is the desired call. The run identity expressing a run of $t+1$ steps as the step after a run of $t$ steps aligns these transitions with the stated time (`runFrom_succ_eq_step'`).

**Key facts.** `Turing.FinTM.f2_loopReady_call`, `Turing.FinTM.f2_loopHost_anchor_return`, `Turing.FinTM.f2_loopHost_release`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
