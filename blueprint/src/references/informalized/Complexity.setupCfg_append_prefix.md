<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_append_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix of the Unary Append Block

**Claim.** After $j$ steps in append phase $0$, the machine is in append phase $j$, its unary head is at $N+j+1$, and the unary tape has markers through $N+j$; all other stated configuration data are unchanged.

**Proof.** Proceed by induction on $j$, using $j\le a+1$ to ensure each transition remains in the append block. The zero-step case is the initial configuration. For the successor step, the induction hypothesis gives phase $j$ and head position $N+j+1$. Since $j<a+1$, the append transition writes a unit marker at that head position, moves the unary head one place right, and advances the phase index to $j+1$; it leaves the input position, other tapes and heads, and output unchanged. The action-on-setup-configurations rule (`Complexity.setupCfg_apply`) records these component changes. The updated unary tape is precisely the tape with one more marker, by the one-cell extension identity (`Complexity.unaryTape_next`), and the zero input movement leaves the input head fixed. This proves the induction step.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.setupCfg_apply`, `Complexity.unaryTape_next`.
