<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitBody_count -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting Phase of the Split-Search Round

**Claim.** If the source machine reaches its halted configuration with output $out$ after $T$ steps, the counting phase of the split-search round reaches the corresponding embedded halted configuration at some time $t\le T$, and avoids the anchor state through time $t$.

**Proof.** Let $c$ be the source configuration at the start and $d$ its stated halted configuration. Choose the first time $t$ at which the source state is halted. Since it is halted at time $T$, this first time satisfies $t\le T$. The source run is stationary after halting (`runFrom_of_halt`), so its configuration at time $t$ is exactly $d$: decompose the run at $T$ into the first $t$ steps and the remaining $T-t$ steps (`runFrom_add`), then use stationarity for the latter. Up to time $t$, the source is live at every earlier time by the minimality of $t$. The simulation fact for the counting phase (`splitCount_run`) therefore identifies each host configuration through time $t$ with the counting embedding of the corresponding source configuration. At time $t$ this is the required embedded halted configuration. At each earlier time, the source is live, and the counting embedding places the host in a counting state rather than the anchor; at time $t$ it is in the return/check state, also not the anchor. Hence the anchor is avoided throughout.

**Key facts.** `Turing.FinTM.splitCount_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
