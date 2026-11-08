<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.back_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Walk over a Unary Register

**Claim.** If register $r$ contains the unary tape of $m$, then for every $d\le m$, a configuration in the return-walk state with its head at $m-d$ reaches the main state for label $\ell$ after $d+1$ steps, with the tape, input position, output, and other heads unchanged and the register-$r$ head at $m$.

**Proof.** We argue by induction on $d$. For $d=0$, the register head is at $m$, the end of the unary tape. Its scanned cell is blank, by the fact that the unary tape has no symbol at or beyond $m$ (`ones_ge`). The return-walk transition therefore moves directly to the main state for $\ell$ without changing the tape, head position, input position, or output. Counting this transition gives the claimed one step.

Now let $d=d_0+1\le m$. The register head starts at $m-(d_0+1)$, a nonnegative position strictly below $m$, so its cell contains $1$ (`ones_lt`). The return-walk transition sees this symbol and moves the head one position to the right, leaving the tape and output unchanged. The head is now at $m-d_0$. By the induction hypothesis, the remaining $d_0+1$ steps return the machine to the main state for $\ell$ with the head at $m$. Altogether there are $1+(d_0+1)=d+1$ steps. The single-step behavior used here is the machine's step decomposition (`step_some`), and run lengths split into a first step followed by the remaining run (`runFrom_succ_eq_step`); the zero-step run is the initial configuration (`runFrom_zero`). The action-application identities (`apply_act`, `apply_ctl`) supply the stated effects on the configuration fields, and `moveInputPos_zero` ensures the input head stays fixed.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.UnaryTape.ones_ge`, `Turing.UnaryTape.ones_lt`, `Turing.moveInputPos_zero`, `Complexity.CounterProg.step_some`, `Complexity.CounterProg.apply_ctl`, `Complexity.CounterProg.apply_act`.
