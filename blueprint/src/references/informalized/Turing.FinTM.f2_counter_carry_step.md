<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_counter_carry_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Counter Carry Step

**Claim.** Starting the counter machine in state $1$ at the boundary after $u$, with tape for $u$ followed by $b$, one step leaves the input head and output unchanged. If $b$ begins with true, the machine remains in state $1$, moves the work head right, and changes that bit to false; otherwise it enters state $2$, moves the work head left, and changes that bit to true.

**Proof.** The transition in state $1$ inspects the work-tape symbol at the head position. The tape-reading fact identifies that symbol with the head of $b$, so the transition branches according to whether that head is true. In the true case it writes false and moves right while retaining state $1$; in the other case it writes true and moves left while entering state $2$. The tape-writing fact identifies each update with the tape for $u$ followed by the written bit and the tail of $b$. The input movement is zero, so the input-head position is unchanged, and the transition emits nothing, leaving the output empty.

**Key facts.** `Turing.FinTM.f2_counterTape_read`, `Turing.FinTM.f2_counterTape_write`, `Turing.moveInputPos_zero`.
