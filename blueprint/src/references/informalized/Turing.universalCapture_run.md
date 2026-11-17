<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCapture_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lockstep capture of a live run

**Claim.** If the underlying machine is not halted at any time $s<t$, then the capture wrapper’s run for $t$ steps from the associated first-phase configuration equals the first-phase configuration associated with the underlying machine’s run for $t$ steps.

**Proof.** Proceed by induction on $t$. At $t=0$, both runs are at their starting configurations, so the claim follows immediately. For the successor step, assume the wrapper tracks the underlying run through time $t$. The hypothesis ensures that the underlying configuration at time $t$ is still live. The one-step capture identity (\texttt{universalCapture\_step}) then says that one further wrapper step produces the first-phase configuration associated with one further underlying-machine step. The successor-run identity (\texttt{runFrom\_succ\_eq\_step'}) expresses both runs at time $t+1$ as one step after their time-$t$ configurations, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.universalCapture_step`.
