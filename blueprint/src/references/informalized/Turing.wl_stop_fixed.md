<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.wl_stop_fixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed configurations at stop states

**Claim.** If a configuration of the loop machine is in stop state $e$, then after any number of steps it remains exactly that configuration.

**Proof.** First show that one step leaves $d$ unchanged. Since its state is $(\mathrm{stop},e)$, the phase-host transition consults the stop-phase redirection rule. That rule returns no successor for every stop control, so the host uses the stop-phase machine. The stop-phase machine is defined to make a stationary transition: it leaves every tape and head position unchanged, emits no output, and keeps the control $e$. Thus the resulting configuration is $d$. Iterating this fixed-point identity, every finite iterate of the step function also sends $d$ to itself, which is the stated conclusion.
