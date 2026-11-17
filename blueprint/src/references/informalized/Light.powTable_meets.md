<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/PowTable.lean :: Light.powTable_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Power Table Procedure Specification

**Claim.** If the program contains the power-table procedure at position $p$ and the stated bounds on memory, word size, and powers hold, then calling it with $(\mathrm{dst},L,b)$ finishes within time $17L+8$, leaves $1,b,\ldots,b^{L-1}$ in the destination segment, and preserves memory outside it.

**Proof.** Apply the power-table execution result to the argument frame containing $\mathrm{dst},L,b$ followed by zero padding. The padded frame agrees with the frame of the four displayed arguments used by that result (`Light.frame_append_zeros`). Thus the procedure body executes within the stated time and produces the required memory properties. Since the program entry at $p$ is that body, the body-execution result lifts to a procedure call (`Light.Meets.of_body`), giving the specification.

**Key facts.** `Light.frame_append_zeros`, `Light.powTable_ends`, `Light.Meets.of_body`.
