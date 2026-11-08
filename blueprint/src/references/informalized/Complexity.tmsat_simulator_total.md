<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_simulator_total -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Simulator Returns the Answer

**Claim.** Under the stated exact-time simulation property, the simulator computes the answer word at the specified time: it outputs $1w$ if the decoded machine halts by time $t$ with output $w$, and outputs $0$ otherwise.

**Proof.** Consider whether the decoded machine's run at time $t$ is in the halting state. If it is, `computesInTime_iff` identifies that run's output as an output computed by the decoded machine in exactly $t$ steps. The first clause of the simulator hypothesis therefore gives the simulator's output as $1$ followed by that run output, which is precisely the answer in the halting case. If the run is not halting, the same characterization shows that the decoded machine computes no output in exactly $t$ steps: any such computation would force its time-$t$ run to be halting. The second clause of the hypothesis then gives output $0$, as required in the nonhalting case.

**Key facts.** `Turing.FinTM.computesInTime_iff`.
