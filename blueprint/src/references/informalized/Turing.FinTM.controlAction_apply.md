<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.controlAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of an input-head control action

**Claim.** Applying a control action with movement $m$ and successor state $q$ to a configuration sets its state to $q$, moves its input head by $m$ with boundary clamping, and leaves its work-tape contents, work-tape head positions, and output unchanged.

**Proof.** The control action specifies the input movement $m$ and state $q$, gives every work tape no write and zero head movement, and emits no symbol. By the definition of applying an action, the new input position is the clamped movement of the old one, and the state becomes $q$. On each work tape, no-write preserves every tape cell, while zero movement preserves its head position. Since no output symbol is emitted, the output list is unchanged.
