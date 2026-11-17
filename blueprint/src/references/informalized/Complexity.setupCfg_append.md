<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Append Block

**Claim.** After $a+2$ steps in append phase $0$, the machine is in borrow phase with carry true; its unary tape has $N+a+1$ markers and its head is at $N+(a+1)+1$, while the other stated data are unchanged.

**Proof.** The prefix-of-append result (`Complexity.setupCfg_append_prefix`) applies with $j=a+1$: after those steps the machine is in append phase $a+1$, with one additional unit marker for each step and unary head at $N+(a+1)+1$. There is one final transition. At index $a+1$ the append condition fails, so the transition changes the phase to borrow with carry true and leaves all tapes and heads fixed. The action-on-setup-configurations rule (`Complexity.setupCfg_apply`) expresses this transition componentwise; since it writes nothing and makes no head movement, the configuration has exactly the claimed form.

**Key facts.** `Complexity.setupCfg_append_prefix`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.setupCfg_apply`.
