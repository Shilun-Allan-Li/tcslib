<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_return -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Return Pass

**Claim.** After $3B+1$ steps from layout-return phase $0$, with the unary head at $B$ and guide head at $3B$, the machine enters layout-left phase $0$ with heads at $1$ and $0$, respectively, leaving the guide tape and all other configuration data unchanged.

**Proof.** The return-prefix formula (`Complexity.setupCfg_layout_return_prefix`) at $j=3B$ puts the machine in layout-return phase $0$, with unary head at $B-B=0$ and guide head at $3B-3B=0$. The unary tape therefore reads its origin marker, by the definition of `unaryTape`. One further step takes the origin-reading branch of layout-return: it enters layout-left phase $0$, moves the unary head right once, and leaves the guide head and both tapes unchanged. The run-successor formula (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) identifies this step with the additional step in the stated run; the resulting heads are at $1$ and $0$.

**Key facts.** `Complexity.setupCfg_layout_return_prefix`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
