<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionMachineTapes.lean :: BoolCircuit.CktSatReduction.Emitter.print_walk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-tape printing walk

**Claim.** Starting with the selected work-tape head at $j-1$ and that tape containing the unary encoding of $m$, the emitter reaches its printing state after $j+1$ steps with the head at zero and with $j$ true bits appended to the output, for every $j\le m$.

**Proof.** Proceed by induction on $j$. For $j=0$, the selected head is at the negative position $-1$, where the unary tape is blank. The printing transition therefore moves the head right into its bit-printing state without writing an output bit; the input head and tape contents remain unchanged, and the selected head is at zero. This is the required configuration with zero true bits appended.

For the successor case, the selected head initially sits at position $j$. Since $j<m$, the unary tape contains a true bit there. The printing transition outputs that bit and moves the head left to position $j-1$, leaving the tape and the other heads unchanged. The induction hypothesis now applies to the remaining $j$ steps, starting from the printing state with head at $j-1$ and the extended output. It returns the head to zero and appends $j$ more true bits. Together with the first bit, this gives $j+1$ appended true bits, and the step counts add to $(j+1)+1$.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `BoolCircuit.CktSatReduction.Emitter.step_some`, `Turing.UnaryTape.ones_neg`, `Turing.UnaryTape.ones_lt`, `Turing.moveInputPos_zero`, `Turing.MultiTapeTM.runFrom_zero`.
