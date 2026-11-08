<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Deterministic.lean :: Turing.MultiTapeTM.workTapePos_step_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Head Movement Bound

**Claim.** After one step of the machine from a configuration $c$, the position of work-tape head $i$ differs from its position in $c$ by at most $1$.

**Proof.** Split according to whether the machine is already in its halting state. If it is halted, a step leaves the configuration unchanged, so the difference is zero. Otherwise, the step applies the transition action to $c$; the head-position bound for applying any action (`workTapePos_apply_le`) gives the required estimate directly.

**Key facts.** `Turing.workTapePos_apply_le`.
