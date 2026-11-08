<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.poolMem_consts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialized Constant Registers

**Claim.** After initializing the constants and pool, the registers at the one, zero, and negative-one addresses contain the word encodings of $1$, $0$, and $-1$, respectively.

**Proof.** The straight-line initialization establishes these three register values (`effects_headStraight_consts`). The pool initialization changes only addresses in its pool region: its memory therefore agrees with the memory immediately after the straight-line initialization at every address outside that region (`agreeOutside_poolCode`). The one, zero, and negative-one addresses lie outside the pool region, so the agreement principle for reading a value outside the changed set (`WordRAM.AgreeOutside.read`) carries each of the three established values through the pool initialization. Together these are the required three equalities.

**Key facts.** `Light.Compiler.effects_headStraight_consts`, `Light.Compiler.agreeOutside_poolCode`, `WordRAM.AgreeOutside.read`.
