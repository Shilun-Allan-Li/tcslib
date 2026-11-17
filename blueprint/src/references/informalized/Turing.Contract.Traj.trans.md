<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.Traj.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Trajectory property for contract composition

**Claim.** For the composed contract, each work-head position through the total duration satisfies the first contract's trajectory property or the second contract's property at the linked datum and first endpoint.

**Proof.** Fix an admissible starting configuration and a time $u$ up to the composed duration. Split into whether $u$ is at most the first contract time. In that case, the first trajectory hypothesis directly gives the first disjunct. Otherwise, write $u=T_1+v$ with $v>0$, where $T_1$ is the first contract time. The run-addition identity (`Turing.MultiTapeTM.runFrom_add`) expresses the run at $u$ as the run for $v$ steps from the configuration reached at time $T_1$. The first contract's endpoint equation identifies that configuration with its postcondition, and its exit property supplies the second contract's entry state. The bound on $u$ gives $v$ no greater than the second contract duration, so the second trajectory hypothesis gives the second disjunct.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`.
