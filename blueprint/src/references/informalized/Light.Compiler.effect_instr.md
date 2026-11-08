<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.effect_instr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Compiled Arithmetic Instruction

**Claim.** If memory cells $j$ and $k$ contain the $W$-bit encodings of $a$ and $b$, then executing the instruction for the arithmetic operation $o$ with destination $i$ writes the $W$-bit encoding of $o(a,b)$ to cell $i$.

**Proof.** Split into the three possible operations. For addition, the compiled instruction is the word-RAM addition instruction, whose effect writes the encoding of $a+b$ to cell $i$ (`WordRAM.effect_add`). For subtraction, the corresponding effect writes the encoding of $a-b$ (`WordRAM.effect_sub`); for multiplication, it writes the encoding of $ab$ (`WordRAM.effect_mul`). In each case the assumed contents of cells $j$ and $k$ supply the two operands, and the operation’s evaluation is exactly the indicated integer operation.

**Key facts.** `WordRAM.effect_add`, `WordRAM.effect_sub`, `WordRAM.effect_mul`.
