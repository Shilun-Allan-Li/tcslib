<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Termination after the unary budget

**Claim.** Under the stated guide and unary-tape conditions, after $B(6R+8)+1$ steps the machine is halted, with unary head at $B+1$ and guide head at $0$.

**Proof.** The repeated-macrostep result says that for every $j\le B$, after $j(6R+8)$ steps the machine is in macrostep-check with unary head at $j+1$ and guide head at $0$ (`macroCfg_repeat`). Apply this at $j=B$: after $B(6R+8)$ steps the head is at $B+1$. The hypothesis `hend` says that cell is blank. Thus the next check step takes the halting branch of the macrostep-check transition (`macroCfg_check`), leaving the head positions unchanged and setting the state to the halted state. The equality between running for one additional step and taking one transition is the run successor rule (`runFrom_succ_eq_step'`).

**Key facts.** `Complexity.macroCfg_repeat`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.macroCfg_check`.
