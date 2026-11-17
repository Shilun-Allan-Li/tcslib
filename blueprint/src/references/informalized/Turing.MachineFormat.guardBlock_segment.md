<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guard block segment phases

**Claim.** The configuration at position $j$ in phase zero has phase-zero state and positive guard time; at every positive time strictly less than its guard time, the state is neither phase zero nor the halting state.

**Proof.** The initial state is phase zero by the definition of the configuration. Its guard time is the minimum of $b+1$ and the number of steps to the right boundary, and both quantities are positive because $b+1>0$ and $j\le |x|$. For any positive $u$ below that guard time, the interior-phase result (Turing.MachineFormat.guardBlock_interior) applies directly and gives a state different from phase zero and from the halting state.

**Key facts.** `Turing.MachineFormat.guardBlock_interior`.
