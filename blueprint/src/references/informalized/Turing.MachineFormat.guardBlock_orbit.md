<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard block orbit advances by full blocks

**Claim.** Iterating the guard machine's counter-loop orbit $r$ times from position $j$ in phase zero gives phase zero at position $j+(b+1)r$, with output unchanged.

**Proof.** Induct on $r$. For $r=0$, the orbit is the starting configuration. For the induction step, the position after $r$ blocks is $j+(b+1)r$, and the hypothesis on the final position ensures this intermediate position is at most $|x|$. It also ensures there is room for another full block, so the guard time there is exactly $b+1$: the input boundary is farther away than one block. Apply the induction hypothesis, then run the guard machine for those $b+1$ steps using the guard block run formula (Turing.MachineFormat.guardBlock_run). The counter returns to phase zero and the position advances by $b+1$, while the output stays unchanged.

**Key facts.** `Turing.MachineFormat.guardBlock_run`.
