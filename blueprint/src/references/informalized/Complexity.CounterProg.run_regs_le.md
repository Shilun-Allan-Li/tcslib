<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.run_regs_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Register Growth

**Claim.** After $t$ steps from any state, each register is at most its initial value plus $t$.

**Proof.** Induct on $t$, generalizing over the starting state. At zero steps the register value is unchanged. For the successor case, decompose the run into one step and the remaining run (`Complexity.CounterProg.run_succ`). The induction hypothesis bounds the register after the remaining run by its value just after the first step plus $t$. A single step increases any fixed register by at most one (`Complexity.CounterProg.step_regs_le`). Together these yield the bound by the initial register value plus $t+1$.

**Key facts.** `Complexity.CounterProg.run_succ`, `Complexity.CounterProg.step_regs_le`.
