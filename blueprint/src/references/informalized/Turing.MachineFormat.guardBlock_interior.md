<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.guardBlock_interior -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Interior guard phases

**Claim.** Under the stated bounds on $u$, after $u$ steps from position $j$ in phase zero, the guard machine is in a phase that is neither phase zero nor the halting state.

**Proof.** The bound on $u$ implies both $u<b+1$ and $j+u\le |x|$. The guard block run formula (Turing.MachineFormat.guardBlock_run) therefore identifies the configuration after $u$ steps as the one at position $j+u$ in phase $u$ modulo $b+1$. Because $u<b+1$, this phase is represented by the residue $u$ itself. Since $u>0$, it differs from phase zero; and the state is a phase, hence is not the halting state.

**Key facts.** `Turing.MachineFormat.guardBlock_run`.
