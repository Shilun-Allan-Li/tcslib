<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes.lean :: BoolCircuit.CktSatReduction.Emitter.back_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Unary-Tape Scan

**Claim.** Starting with the head of tape $t$ at cell $m-d$ in state $\mathrm{pr}(k,c,pc,t)$, the machine reaches $\mathrm{em}(k,c,pc+1)$ after $d+1$ steps, with the head at cell $m$ and all other configuration data unchanged.

**Proof.** Fix $d\le m$ and induct on $d$. When $d=0$, the head is at cell $m$, where the unary tape is blank by the blank-cell property of $\mathrm{ones}$ ($\texttt{Turing.UnaryTape.ones\_ge}$). The transition therefore takes the control branch to the emission state; the control action leaves the tapes, heads, and output unchanged, and does not move the input head ($\texttt{Turing.moveInputPos\_zero}$). This is the required one-step run, using the zero-step and successor-run identities ($\texttt{Turing.MultiTapeTM.runFrom\_zero}$ and $\texttt{Turing.MultiTapeTM.runFrom\_succ\_eq\_step}$). For the induction step, write $d=d'+1$. The head is then at $m-(d'+1)$, a nonnegative cell strictly below $m$, so it reads $1$ by the unary-tape interior property ($\texttt{Turing.UnaryTape.ones\_lt}$). The transition writes nothing, moves tape $t$ one cell to the right, and continues the scan. Since $m-(d'+1)+1=m-d'$, the new configuration is precisely the induction hypothesis's starting configuration. Applying that hypothesis completes the remaining $d'+1$ steps and yields the claimed endpoint; the other configuration data remain unchanged throughout.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `Turing.UnaryTape.ones_ge`, `Turing.moveInputPos_zero`, `Turing.UnaryTape.ones_lt`, `BoolCircuit.CktSatReduction.Emitter.apply_ctl`, `BoolCircuit.CktSatReduction.Emitter.apply_act`.
