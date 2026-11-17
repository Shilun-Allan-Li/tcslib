<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.snap_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot Instruction Bits

**Claim.** Under the stated register assumptions and with $t\le T$, executing the snapshot template at time $t$ outputs the instruction-bit list for the snapshot position recorded in the instruction register.

**Proof.** Apply the general template-to-instruction output result (`prog_instr_bits`) to the snapshot template, using the source list `snapSrcs` for time $t$. The bound `snapIdx_lt_succ` places the instruction index below the end of the tableau program: the snapshot at time $t$ lies within the first $t+1$ configuration strides, and $t\le T$ gives the required program bound. The position-identification result `cfgPos_snapIdx` says that this index is precisely the snapshot position at time $t`; hence `cfgInstr` has snapshot kind and its padded sources are exactly the sources supplied to the template.

The source correspondence is established by `snapS_toBitSrc`: when the instruction register is the snapshot index, the current-step register is $T$, and the step-start register is $t$ times the stride, translating each snapshot-template source yields the corresponding tableau source list. Padding commutes with this translation by `padS_toBitSrc`. Finally, each source is admissible: `ok_snapS` verifies the snapshot sources from the positive instruction index and, when the template is not at time zero, the positive step-start register; `ok_padS` preserves admissibility after padding. The register equalities identify these register values with the hypotheses, and the positive step-start value follows from $t\ne0$ and the positive stride. These facts provide all conditions for `prog_instr_bits`, which gives the claimed output equality.

**Key facts.** `Complexity.UTab.prog_instr_bits`, `Complexity.snapIdx_lt_succ`, `Complexity.cfgPos_snapIdx`, `Complexity.length_tabLayout`, `Complexity.UTab.snapS_toBitSrc`, `Complexity.UTab.padS_toBitSrc`, `Complexity.UTab.ok_padS`, `Complexity.UTab.ok_snapS`.
