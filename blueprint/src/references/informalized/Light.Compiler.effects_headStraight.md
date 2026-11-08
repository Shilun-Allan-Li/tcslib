<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.effects_headStraight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effects of Head Initialization

**Claim.** Executing the head-initialization code sets the constant-one cell to the word value $1$, the zero cell to $0$, and the negative-one cell to $-1$, in that order.

**Proof.** The code consists of a one-instruction write of $1$ to the constant-one cell, followed by two subtractions. The first subtracts that cell from itself and writes $0$ to the zero cell; the second subtracts the constant-one cell from the newly initialized zero cell and writes $-1$ to the negative-one cell. The effects of a list follow the effects of its instructions in sequence (`effects_cons`), with the empty suffix leaving memory unchanged (`effects_nil`). The instruction-effect formulas for a direct write and subtraction (`effect_one`, `effect_sub`) give the three nested memory updates in the claimed order.

**Key facts.** `WordRAM.effects_cons`, `WordRAM.effects_nil`, `WordRAM.effect_one`, `WordRAM.effect_sub`.
