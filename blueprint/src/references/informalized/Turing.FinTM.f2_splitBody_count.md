<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitBody_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Split-Body Simulation

**Claim.** If the simulated run on the empty input, started in state $a$ with the bank tape initialized from $s$, halts after exactly $T$ steps with output $o$, then the split-body machine reaches the corresponding count configuration for the halted run after some $t≤T$ steps and avoids its anchor state through that time.

**Proof.** Let $c$ be the simulated starting bank configuration and $d$ the specified halted configuration. Since the simulated run is halted at time $T$, there is a first halting time $t≤T$ (choose the least halting time among those no greater than $T$). The run at this first halting time equals $d$: extending it to time $T$ leaves it unchanged because halted runs stay fixed (Turing.MultiTapeTM.runFrom_of_halt), while the run at $T$ is $d$, using the run-addition identity (Turing.MultiTapeTM.runFrom_add). For every $j≤t$, minimality of $t$ ensures the simulated run is live at every earlier time. The count-mode simulation lemma (Turing.FinTM.f2_splitCount_run) therefore identifies the split-body machine's configuration at time $j$ with the count encoding of the simulated configuration at time $j$. At $j=t$, this identification and the equality with $d$ give the required terminal count configuration. At every $j≤t$, the encoded state is either a count state for a live simulated state or the return state for a halted simulated state; neither is the anchor state. Thus the run remains safe through time $t$.

**Key facts.** `Turing.FinTM.f2_splitCount_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
