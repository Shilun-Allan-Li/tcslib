<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes.lean :: BoolCircuit.CktSatReduction.Emitter.clear_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing a Unary Tape

**Claim.** From state $\mathrm{clW}(t)$ with tape $t$ containing ones in cells $0$ through $j-1$ and its head at $j-1$, the machine reaches $\mathrm{clS2}$ when $t=1$ and $\mathrm{inc}$ otherwise, after $j+1$ steps. Tape $t$ is blank with its head at zero, and all other configuration data are unchanged.

**Proof.** Induct on $j$. For $j=0$, the head is at cell $-1$, which is blank by the negative-cell property of the unary tape ($\texttt{Turing.UnaryTape.ones\_neg}$). The machine takes its blank-cell transition, which sets the head to zero and leaves the tape blank; it does not move the input head ($\texttt{Turing.moveInputPos\_zero}$). For the successor case, the head begins at cell $j$, which contains $1$ because $0\le j<j+1$ and hence the unary-tape interior property applies ($\texttt{Turing.UnaryTape.ones\_lt}$). The machine erases that cell and moves left, so the tape's contents become $\mathrm{ones}(j)$: erasing the last one from $\mathrm{ones}(j+1)$ gives $\mathrm{ones}(j)$ ($\texttt{Turing.UnaryTape.update\_ones\_pred}$). The head moves from $j$ to $j-1$, putting the configuration in the induction hypothesis's starting form. The induction hypothesis then clears the remaining $j$ ones and establishes the specified final state and head position. In both cases the transition leaves the input head, other tapes and heads, and output unchanged. The run identities split off the first step and identify the zero-step remainder ($\texttt{Turing.MultiTapeTM.runFrom\_succ\_eq\_step}$ and $\texttt{Turing.MultiTapeTM.runFrom\_zero}$).

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.UnaryTape.ones_neg`, `BoolCircuit.CktSatReduction.Emitter.apply_act`, `Turing.moveInputPos_zero`, `Turing.UnaryTape.ones_lt`, `Turing.UnaryTape.update_ones_pred`.
