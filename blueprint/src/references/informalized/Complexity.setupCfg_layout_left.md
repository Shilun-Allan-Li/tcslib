<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Leftward Allocation Pass

**Claim.** For $B>0$, starting at the first leftward layout phase with the stated unary tape and right guide, after $3B+2$ steps the machine is in unary-reset phase with unary head at $B$ and guide head at $-3B-1$ over the completed radius-$3B$ guide.

**Proof.** Use `setupCfg_layout_prefix` for $3B$ steps in the leftward direction. It places the allocation phase at index $0$ (since $3B$ is divisible by $3$), the unary head at $B+1$, and the guide head at $-3B$, with the guide filled through those $3B$ cells. The guide retains its origin mark by `rightGuide_origin`, so the endpoint transition `setupCfg_layout_end` applies: it enters left-edge phase, writes an interior mark at the current guide position, and moves the guide head left. The next transition, from left-edge phase, enters unary-reset and writes the left edge marker without moving either head. The resulting two guide updates complete the guide tape by `guideFill_left_finish`; the unary head is then at $B$, and the guide head is at $-3B-1$. The run-step decomposition accounts for the total of $3B+2$ steps.

**Key facts.** `Complexity.setupCfg_layout_prefix`, `Complexity.rightGuide_origin`, `Complexity.setupCfg_layout_end`, `Complexity.guideFill_left_finish`, `Complexity.setupCfg_apply`.
