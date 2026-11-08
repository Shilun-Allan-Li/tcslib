<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.run_run_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Simulation from Yard Position Zero

**Claim.** For any configuration $a$ of $A$ and choice word $u$ with $|u|\le m$, running the host on $u$ from the representation of $a$ with yard head at zero yields the representation of $A$'s run on $u$ from $a$, with yard head at $|u|$.

**Proof.** Apply the general clocked-run simulation `run_run` at initial yard position $j=0$. Its required bound $0+|u|\le m$ is exactly the hypothesis. The resulting yard position is the natural number $|u|$ viewed as an integer, which is the position used in the stated representation.

**Key facts.** `Turing.ClockHost.run_run`.
