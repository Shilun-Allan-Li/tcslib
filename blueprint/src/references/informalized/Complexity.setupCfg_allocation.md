<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_allocation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion of the Guide Allocation

**Claim.** After the stated allocation interval, the schedule machine is in macrostep-check phase, with the unary head at $1$ and the guide head at $0$ over the guide of radius $3B$, while the other specified configuration data are unchanged.

**Proof.** The proof composes the machine's established phase-by-phase run descriptions. First, `Complexity.setupCfg_unary_start` takes $B+2$ steps from unary-start to layout-right, leaving the unary head at $1$. The layout-right run (`Complexity.setupCfg_layout_right`) takes $3B+2$ steps, placing the guide at the right edge of the allocated guide and the unary head at $B$. The return pass (`Complexity.setupCfg_layout_return`) takes $3B+1$ steps and reaches layout-left with unary head at $1$. The layout-left run (`Complexity.setupCfg_layout_left`) takes $3B+2$ steps, completing the guide of radius $3B$ and positioning the heads for the reset. The unary rewind description (`Complexity.setupCfg_unary_rewind`), with its final flag set, takes $B+1$ steps and moves the unary head back to $1$, entering start-center with guide head at $-(3B)-1$. Finally, `Complexity.setupCfg_start_center` takes $3B+2$ steps, returning the guide head to $0$ and entering macrostep-check. The step counts sum to $14B+10$; each phase lemma preserves the base data, budget tape and head, and output, as required.

**Key facts.** `Complexity.setupCfg_unary_start`, `Complexity.setupCfg_layout_right`, `Complexity.setupCfg_layout_return`, `Complexity.setupCfg_layout_left`, `Complexity.setupCfg_unary_rewind`, `Complexity.setupCfg_start_center`, `Turing.MultiTapeTM.runFrom_add`.
