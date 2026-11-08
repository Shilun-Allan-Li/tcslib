<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.prog_instr_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding Configuration Instruction Bits

**Claim.** Under the stated agreement between the template sources and the configuration instruction, executing the template operations with register values $e$ produces exactly the encoded bits of that instruction.

**Proof.** First, the valid layout of the tableau input implies that every instruction in the generated configuration program has exactly the prescribed configuration arity, and that its sources are valid at the instruction index (cfgProg_wf, using tabLayout_valid). The length formula for that program, together with the range hypothesis on $e.I$ and the length of the input layout, shows that the selected index is in range (length_cfgProg and length_tabLayout). The selected instruction is therefore precisely the configuration instruction at that index (cfgProg_getElem). By the assumed identification of that instruction, its kind is $\theta.kind$ and its source list is the padded list of $srcs$. The assumed translation equality identifies the template's translated sources with this list; the source-validity hypothesis supplies validity for those template sources. The instruction-encoding theorem now applies: the template operations, executed with the given register values, produce the bits encoding the selected instruction. Replacing that instruction by its identified configuration instruction gives exactly the definition of $ibits$ at index $e.I$ (instr_bits).

**Key facts.** `Complexity.length_cfgProg`, `Complexity.length_tabLayout`, `Complexity.cfgProg_getElem`, `Complexity.cfgProg_wf`, `Complexity.tabLayout_valid`, `Complexity.UTab.instr_bits`.
