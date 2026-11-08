<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Finite.lean :: Turing.FinTM.ComputesInTime.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Time Bounds

**Claim.** If the machine computes $w$ from $x$ within $t$ steps and $t\leq t'$, then it computes $w$ from $x$ within $t'$ steps.

**Proof.** The computation at time $t$ has halted with output $w$. Since a halted configuration remains fixed, running for any additional number of steps leaves that configuration unchanged. In particular, the run at time $t'=t+(t'-t)$ is the same configuration as at time $t$: decompose the run into these two durations using `runFrom_add`, then use the fact that running from a halted configuration does not change it (`runFrom_of_halt`). The machine is thus still halted with output $w$ at time $t'$, and its space-use witness is supplied by the definition of computation within time.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_of_halt`.
