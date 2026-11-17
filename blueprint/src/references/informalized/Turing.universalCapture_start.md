<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCapture_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entry into the interpreter after halting

**Claim.** If the underlying machine is halted after $T$ steps from its initial configuration on $x$, then at some time $t\le T+1$ the capture wrapper is in the interpreter-entry configuration associated with that halted configuration.

**Proof.** Consider the set of times at which the underlying run from its initial configuration is halted. It is nonempty, since it contains $T$; let $t$ be its least element. Then $t\le T$, and the configuration at time $t$ is halted. The run is stationary after reaching a halted configuration (\texttt{runFrom\_of\_halt}), so its configurations at times $T$ and $t$ coincide: write $T=t+d$ and apply the run concatenation law (\texttt{runFrom\_add}). Up to but not including time $t$, the underlying run is live by minimality of $t$. The lockstep capture result (\texttt{universalCapture\_run}) therefore identifies the wrapper’s configuration after $t$ steps with the first-phase configuration associated with the underlying halted configuration at time $t$. One additional wrapper step transfers a halted first-phase configuration into interpreter mode (\texttt{universalCapture\_transfer}). By the successor-run identity (\texttt{runFrom\_succ\_eq\_step'}), the wrapper at time $t+1$ is thus in the interpreter-entry configuration associated with the run at time $t$, which equals the run at time $T$. Since $t\le T$, this time satisfies $t+1\le T+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.universalCapture_init`, `Turing.universalCapture_run`, `Turing.universalCapture_transfer`.
