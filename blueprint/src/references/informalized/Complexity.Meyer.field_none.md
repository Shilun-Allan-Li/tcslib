<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.field_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting on an invalid field

**Claim.** When reading a field from the remaining input returns no result, the tabulating machine halts within the stated number of steps and outputs [false].

**Proof.** Proceed by cases on the shape of the remaining word. If it begins with a bit followed by the field-continuation marker true, the decoder must continue on the tail after those two bits; its failure there is the recursive hypothesis. The suffix lookup fact (getElem?_of_drop) identifies these first two bits at the corresponding input positions. The machine's transition facts show that it consumes the pair in two steps, updating the auxiliary words according to the flag, and then reaches the recursive starting configuration on the shorter suffix (pcfg_fA and pcfg_fB_true). Apply the recursive bound to that suffix and add the two consumed steps; the resulting total is at most the original suffix length plus one. If the second bit is false, the decoder would terminate successfully, contradicting the assumed failure. If the remaining word is empty, the next input position has no symbol; the machine rejects in one step, halting with output [false] (pcfg_reject). If it consists of one bit, the machine consumes that bit and then encounters the end of input, where it rejects; this takes two steps and gives the same output. The bounds in these last cases follow directly from their suffix lengths.

**Key facts.** `Complexity.Meyer.getElem?_of_drop`, `Complexity.Meyer.pcfg_fA`, `Complexity.Meyer.pcfg_fB_true`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.Meyer.pcfg_reject`, `Turing.MultiTapeTM.runFrom_zero`.
