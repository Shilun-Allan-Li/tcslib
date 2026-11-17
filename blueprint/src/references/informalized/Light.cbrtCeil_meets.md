<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Logs.lean :: Light.cbrtCeil_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ceiling Cube-Root Program Execution

**Claim.** Under the stated word-bound hypothesis, the specified program called with input $n$ finishes within $12r+12$ steps, where $r$ is the least natural number with $n\le r^3$. It returns $r$ in location $0$ and leaves memory unchanged.

**Proof.** First, `Meets.of_body` reduces the claim to executing the specified body from the initial frame. After setting the candidate to $0$, analyze the loop with invariant that, before round $i$, the state has candidate $i$, input $n$, and memory $\mu$. For each $i<r$, minimality of $r$ gives $i^3<n$ (`pow_lt_of_lt_cbrtLeast`). Thus the loop condition holds, and incrementing the candidate establishes the invariant for round $i+1$. The bound on the word size ensures the loop test and increment are safe (`abs_cube_le`); the update to the local frame is described by `update_frame_setLocal`. The invariant starts at $i=0$. At round $r$, the defining property of $r$ gives $n\le r^3$ (`le_cbrtLeast_pow`), so the loop condition is false. The final assignment copies the candidate into the argument location, yielding $r$ there and preserving memory. `Ends.whileBlock` packages these rounds and their stated cost bound, and `Ends.next` combines the initial assignment, loop, and final assignment within the specified time. The body lookup hypothesis then gives the required program call.

**Key facts.** `Light.Meets.of_body`, `Light.Ends.next`, `Light.Ends.whileBlock`, `Light.pow_lt_of_lt_cbrtLeast`, `Light.abs_cube_le`, `Light.update_frame_setLocal`, `Light.le_cbrtLeast_pow`.
