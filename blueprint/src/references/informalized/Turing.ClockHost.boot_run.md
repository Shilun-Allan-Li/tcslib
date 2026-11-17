<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.boot_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boot Run Simulation

**Claim.** If the simulated deterministic machine remains running at every time strictly before $|w|$, then the host machine run on $w$ from the boot configuration of $c$ equals the boot configuration reached by running the simulated machine for $|w|$ steps.

**Proof.** Induct on the choice word, generalizing the starting configuration. For the empty word, both sides are the boot configuration of $c$. For a word $b::w$, the liveness hypothesis at time $0$, together with the zero-step run identity (`runFrom_zero`), shows that $c$ has some state $q$. The one-step boot simulation (`boot_step`) then identifies the host's first step under $b$ with the boot configuration of the simulated machine's one-step successor. The run-on-a-cons identity (`runWith_cons`) expresses the remaining host run on $w$ from that successor. Apply the induction hypothesis there: its required liveness condition follows by translating each time $t$ after the first step to time $t+1$ in the original run, using the successor-time identity (`runFrom_succ_eq_step`). The resulting simulated run has length $|w|+1$, again by that identity, and this is the claimed equality.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`, `Turing.ClockHost.boot_step`, `Turing.NDTM.runWith_cons`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
