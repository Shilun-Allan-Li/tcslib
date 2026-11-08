<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix of an Outward Allocation Pass

**Claim.** After $j$ steps, for $j\le 3B$, the allocation index is $j$ modulo $3$, the unary head is at $\lfloor j/3\rfloor+1$, and the guide head is at $j$ to the right or $-j$ to the left, with the guide filled through $j$ cells in that direction.

**Proof.** Proceed by induction on $j$. At $j=0$, the phase index and both head positions have their initial values, and `guideFill_zero` says that filling zero cells leaves the guide unchanged. For the successor step, the induction hypothesis and $j+1\le 3B$ ensure that the current unary head is still over a unit marker; this is `unaryTape_unit` applied at position $\lfloor j/3\rfloor$. The origin condition for the partially filled guide follows from the assumed origin condition and `guideFill_origin`. Hence `setupCfg_layout_fill` gives the next configuration: the guide head moves one cell in the chosen direction, the unary head advances exactly when the phase index is $2$, and the guide extends by one cell. `nextThird_mod` identifies the new index with $(j+1)\bmod 3$. The quotient and head-position identities follow from the elementary division-by-three cases.

**Key facts.** `Complexity.guideFill_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.unaryTape_unit`, `Complexity.setupCfg_layout_fill`, `Complexity.nextThird_mod`.
