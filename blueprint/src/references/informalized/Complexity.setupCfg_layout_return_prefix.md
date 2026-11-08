<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_layout_return_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix of the Return Sweep

**Claim.** For each $j\le 3B$, after $j$ steps the machine is in layout-return phase $j\bmod 3$, with unary head at $B-\lfloor j/3\rfloor$ and guide head at $3B-j$, while tape contents and all other configuration data remain unchanged.

**Proof.** Proceed by induction on $j$. At $j=0$, the stated configuration is the initial one. For the successor step, apply the induction hypothesis and use $j<3B$. This inequality implies $\lfloor j/3\rfloor<B$, so the unary head is at a positive position and cannot read the origin marker: `unaryTape_origin` says the origin marker occurs exactly at position zero. Thus the return-step rule applies (`Complexity.setupCfg_layout_return_step`): it advances the phase index by `nextThird`, moves the guide head left once, and moves the unary head left exactly when the current phase index is $2$. The modular identity `nextThird_mod` identifies the new phase index with $(j+1)\bmod 3$. Since the phase index is $j\bmod 3$, its value is $2$ exactly when division of $j$ by $3$ gains one in passing to $j+1$; hence the unary position becomes $B-\lfloor (j+1)/3\rfloor$. The guide position becomes $3B-(j+1)$, and no tape is written during these return steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.unaryTape_origin`, `Complexity.setupCfg_layout_return_step`, `Complexity.nextThird_mod`.
