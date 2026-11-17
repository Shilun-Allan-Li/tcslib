<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.rel_startMem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relation After Initialization

**Claim.** Under the stated size, memory, and argument-register assumptions, the initialization program leaves a machine memory related at stack index $4$ to the light state with local values $0,i,j$ and memory $\mu$.

**Proof.** First initialize the constant registers and pool. The constant-register result (`poolMem_consts`) supplies the encodings of $1,0,-1$, and the pool result (`poolMem_pool`) supplies the encoding of each required pool offset. The pool initialization preserves all addresses outside its designated region (`agreeOutside_poolMem`), so in particular the argument registers retain the encodings of $i$ and $j$ and all initially specified machine-memory cells retain their encodings of $\mu$. Next run the frame initialization. Its effect is described by `effects_frameCode`: it sets the frame pointer to the stack address for index $4$, zeroes the frame’s local slots, and writes the argument values into slots $1$ and $2$. The zeroing property of the zeroing code (`effects_zeroCode`) gives value zero in every other local slot; the two argument slots contain $i$ and $j$ by the frame-code calculation. Finally, frame initialization preserves addresses outside its frame region (`agreeOutside_frameCode`), which carries forward the constant and pool values and the represented memory. These facts give, respectively, all fields of the required relation: constants, pool, frame pointer, locals, and memory. The list decomposition `startMem_eq` identifies these two stages with the stated initialization program.

**Key facts.** `Light.Compiler.poolMem_consts`, `Light.Compiler.poolMem_pool`, `Light.Compiler.agreeOutside_poolMem`, `Light.Compiler.effects_frameCode`, `Light.Compiler.effects_zeroCode`, `Light.Compiler.agreeOutside_frameCode`, `Light.Compiler.startMem_eq`.
