<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.step_straight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a straight instruction

**Claim.** If the instruction at $c$'s program counter is a straight instruction, then one step advances the program counter by one and changes the memory to the effect of that instruction on $c$'s memory.

**Proof.** First observe that the memory function used by the step definition, which takes the new value at the target address and agrees with the old memory elsewhere, is exactly the function obtained by updating the old memory at that address. Now split into the possible forms of the instruction. Since it is straight, it must be one, addition, subtraction, multiplication, load, or store. In each case, the defining branch of the step function advances the program counter by one and writes the value prescribed by the corresponding case of the effect function. For the one instruction, the literal one is the word representing the integer one ($\mathrm{wd\_one}$); the other cases use the same values in both definitions. Hence the resulting configuration has the asserted memory and program counter.

**Key facts.** `WordRAM.wd_one`.
