<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.agreeOutside_poolMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory preserved outside the constants

**Claim.** After initializing the three constant cells and then the pool, memory agrees with its original value outside the union of the constant addresses and the pool addresses.

**Proof.** First, the straight-line initialization establishes the stated memory updates at the three constant addresses (\texttt{Light.Compiler.effects_headStraight}). Starting from the original memory, these updates preserve agreement outside the constants, by reflexivity of agreement and the update property of agreement outside a set (\texttt{WordRAM.AgreeOutside.refl}, \texttt{WordRAM.AgreeOutside.update}). Next, pool initialization preserves agreement outside the pool (\texttt{Light.Compiler.agreeOutside_poolCode}). Combining these two preservation statements gives agreement outside the union of the constants and pool (\texttt{WordRAM.AgreeOutside.trans_union}).

**Key facts.** `Light.Compiler.effects_headStraight`, `WordRAM.AgreeOutside.refl`, `WordRAM.AgreeOutside.update`, `Light.Compiler.agreeOutside_poolCode`, `WordRAM.AgreeOutside.trans_union`.
