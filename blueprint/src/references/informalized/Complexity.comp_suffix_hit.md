<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.comp_suffix_hit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix-Hit Halting Result

**Claim.** From the suffix-hit state, the machine halts with true when mode is true, and otherwise with the input bit at register $0$, interpreted as false beyond the input; the precondition and register bound hold throughout.

**Proof.** Split on the mode flag. When it is false, the suffix-hit instruction calls the input-bit decider on the whole input at the index in register $0$, then branches to the corresponding answer state. The input-bit oracle returns exactly that indexed bit (`comp_bit`), so the call-and-return result (`comp_call_return`) proves the desired halting answer and preserves the required configuration conditions. When mode is true, the suffix-hit instruction returns true immediately. The initial precondition and register bound follow from `comp_preS` and the assumed register bound, so the return-state halting result (`AHalt.ret`) applies.

**Key facts.** `Complexity.comp_bit`, `Complexity.comp_call_return`, `Complexity.comp_preS`, `Complexity.LogProg.AHalt.ret`.
