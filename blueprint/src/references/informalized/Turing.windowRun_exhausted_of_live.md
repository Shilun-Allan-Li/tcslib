<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.windowRun_exhausted_of_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exhaustion of a Live Window Run

**Claim.** If the machine remains live before time $N$ and its configurations through time $N$ stay in the window, the window run exhausts its clock and returns the machine's configuration at time $N$.

**Proof.** Proceed by induction on $N$. For $N=0$, the window run is defined to return the exhausted outcome and its input configuration, which is also the zero-step run. For the induction step, the liveness assumption at time $0$ says the initial configuration is not halted. The window assumption at time $1$ says its one-step successor is still in the window. Therefore the recursive definition of the window run takes its continuing branch: it performs that step, updates the accumulator, and invokes a window run with clock $N$ from the successor. Apply the induction hypothesis to this successor. Its liveness condition at each time $u<N$ follows from the original liveness condition at time $u+1<N+1$, using the successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`); likewise, its window condition through time $N$ follows from the original window condition through time $N+1$. The recursive run therefore exhausts its clock and ends at the successor's time-$N$ configuration, which is the original run's time-$(N+1)$ configuration by the same identity.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`.
