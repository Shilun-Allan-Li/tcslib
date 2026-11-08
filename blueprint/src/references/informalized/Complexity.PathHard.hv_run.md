<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.hv_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving the Source Register

**Claim.** Starting from phase $0$ of the halving routine, the program reaches the copy routine with the loop counter reset to $0$ and the source register equal to its original value divided by $2$ to the power of its original loop-counter value; all earlier configurations satisfy the register bound and instruction preconditions.

**Proof.** Apply the bounded halving-loop result (`Complexity.LogProg.halve_run`) to the three instructions of this routine: test whether the counter is zero, decrement it if not, and halve the source before returning to the test. The counter and source are distinct registers, as witnessed by the concrete register indices. With the initial counter value taken as the loop parameter, the loop result clears that counter and replaces the source by its initial value divided by $2$ to that parameter. The state bound supplies the required bound for every register, and the loop result includes the guard at every configuration before the endpoint. Identifying the updated register function with the displayed structured state gives the claimed endpoint.

**Key facts.** `Complexity.LogProg.halve_run`, `Complexity.PathHard.St.Bd.toV`.
