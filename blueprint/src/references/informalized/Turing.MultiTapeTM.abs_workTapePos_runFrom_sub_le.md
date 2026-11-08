<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.MultiTapeTM.abs_workTapePos_runFrom_sub_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Head Displacement Bound

**Claim.** For a multi-tape Turing machine with Boolean symbols, a configuration $d$, a time $t\in\mathbb{N}$, and a work-tape index $j$, the absolute displacement of head $j$ after $t$ steps is at most $t$.

**Proof.** Let $h(u)$ be the position of head $j$ after $u$ steps from $d$. Each individual step moves that head by at most one: the successor-step identity for a run (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies the next configuration as one machine step, and the one-step head-displacement bound (`Turing.MultiTapeTM.workTapePos_step_le`) gives $|h(u+1)-h(u)|\le 1$. The total displacement telescopes as $h(t)-h(0)=\sum_{u<t}(h(u+1)-h(u))$. The triangle inequality for finite sums bounds its absolute value by the sum of the absolute values of these increments, which is at most $\sum_{u<t}1=t$. Since $h(0)=d$'s head position, this is the claimed bound.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.workTapePos_step_le`.
