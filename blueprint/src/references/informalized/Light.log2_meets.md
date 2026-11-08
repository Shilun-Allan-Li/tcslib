<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.log2_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithm routine time bound

**Claim.** If procedure $p$ is the base-two logarithm routine and the word limit is at least $2x+2$, then calling it with input $x$ returns $\lfloor\log_2 x\rfloor$, preserves memory, and finishes within $14\lfloor\log_2 x\rfloor+12$ steps.

**Proof.** First, $x<2^{\lfloor\log_2 x\rfloor+1}$, so after the loop has taken $i$ rounds, the candidate count is $i$ and the power register is $2^{i+1}$; the input and memory remain unchanged. This is the loop invariant used to analyze the execution. The initial assignments set the count to $0$ and the power to $2$. For each $i<\lfloor\log_2 x\rfloor$, the power satisfies $2^{i+1}\le x$, so the loop test succeeds. The body doubles the power and increments the count, establishing the invariant for round $i+1$. The bound $2x+2$ ensures the expressions and tests in these rounds are safe. At $i=\lfloor\log_2 x\rfloor$, the strict upper bound on $x$ makes the test fail; the final assignment copies the count into the argument register, yielding the claimed logarithm. The loop execution is assembled using the repeated-round bound for a loop (`Ends.whileBlock`), and the initial assignments and loop are combined into an execution of the whole body (`Ends.next`). The body is then identified with procedure $p$ and its execution is converted to the stated calling guarantee (`Meets.of_body`). Updating the local frame in the assignments preserves the intended argument and count registers (`update_frame_setLocal`).

**Key facts.** `Light.Ends.whileBlock`, `Light.Ends.next`, `Light.update_frame_setLocal`, `Light.Meets.of_body`.
