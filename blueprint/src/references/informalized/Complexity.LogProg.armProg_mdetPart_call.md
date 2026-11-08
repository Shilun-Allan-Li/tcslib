<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.armProg_mdetPart_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Memory Replacement Preserves Calls

**Claim.** Retaining deterministic instructions and replacing each memory instruction by a return of either Boolean value yields compiled register programs with identical call maps.

**Proof.** Fix a state-phase pair $(l,ph)$ and inspect the instruction $A(l)$. If it is deterministic, both replacements retain that instruction, so their call specifications agree. Otherwise, it is a memory instruction, and either replacement turns it into a return, with the chosen Boolean value. Returns produce no call specification at any phase, so the call specifications agree in this case as well. Equality at every state-phase pair proves equality of the call maps.

**Key facts.** `Complexity.LogProg.MARM.detPart_det`, `Complexity.LogProg.MARM.detPart_mem`.
