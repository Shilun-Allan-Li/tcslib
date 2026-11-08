<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.instr_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Template and Tableau Instruction Bits

**Claim.** If the template’s evaluated sources match the instruction’s sources and the stated kind, length, and validity conditions hold, executing the template produces exactly the encoded bits of the tableau instruction.

**Proof.** Replace the template’s operation list by its instruction-operation list using the assumed equality. The execution identity for instruction operations (`instrOps_exec`) then expresses the output as two consecutive encodings: copy gates at the evaluated template-source positions, and the fixed gates for the template kind shifted by the value of the base expression. The encoding of a concatenation splits into these two encodings (`gbits_append`), and the kind assumption identifies the fixed gates with those for the given instruction.

It remains to identify the copy-gate block. Since the instruction source list has length equal to the configuration arity, padding it to that arity leaves it unchanged. The source-evaluation assumption says that the evaluated template sources are exactly this list. For each source, its validity and the corresponding template-source validity allow the address identity `tabSrc_toBitSrc` to be applied: the tableau address assigned to the evaluated source is the value of its linear expression at the register record. Thus every copy gate in the first encoding is the copy gate selected by the corresponding instruction source in `tabInstrGates`. The second encoding already consists of the fixed gates shifted by the evaluated base, which `baseE_val` identifies with the tableau base at instruction index $e.i$. Together these identifications give the encoded tableau instruction.

**Key facts.** `Complexity.UTab.instrOps_exec`, `Complexity.UTab.gbits_append`, `Complexity.UTab.baseE_val`, `Complexity.UTab.tabSrc_toBitSrc`.
