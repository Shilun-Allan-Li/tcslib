<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.boot_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boot Step Simulation

**Claim.** If the simulated configuration $c$ has state $q$, then one host-machine step from its boot configuration equals the boot configuration of the one-step successor under the deterministic machine.

**Proof.** The boot configuration has host state equal to the boot phase carrying $q$. Thus the host step uses the boot branch of its transition rule. At each yardstick tape, the boot configuration presents exactly the symbols read by the corresponding tape of $c$; its input symbol is also the same. Therefore the transition chosen by the host in the boot phase is the deterministic machine's transition on $c$. The state-step rule (`stepWith_of_state`) justifies using that transition because the host state is nonempty, and the deterministic step is its transition action applied to $c$. Finally, applying the action to the host configuration updates the grouped tapes and head positions componentwise (`apply_hostCfg`). The host's output tape stores the deterministic output word as a buffer tape. If the transition emits no bit, that buffer tape and output word remain unchanged; if it emits a bit, appending it updates the buffer tape at the former word length (`bufferTape_append`). In either case the resulting host configuration is precisely the boot configuration of the deterministic successor.

**Key facts.** `Turing.NDTM.stepWith_of_state`, `Turing.ClockHost.apply_hostCfg`, `Turing.FinTM.bufferTape_append`.
