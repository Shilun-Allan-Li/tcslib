<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.detM_tr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Transition Independence

**Claim.** At a state where the memory-choice map is undefined, the deterministic compilation has the same transition for every answer parameter.

**Proof.** Compare the compiled transition functions using the congruence result for compiled transitions (`ctr_congr`). Their call maps agree for all answer parameters (`armProg_mdetPart_call`). It remains to compare ordinary transitions at a program-running state. Write its program component as $l$ and its phase as $\mathrm{ph}$, and split on the instruction at $l$. If it is a deterministic instruction, both deterministic-part programs retain that same instruction (`MARM.detPart_det`), so their transitions agree. Otherwise the instruction is a memory operation. The hypothesis that the memory-choice map is undefined rules out phase $\mathrm{start}$ at this state: there the map would be defined by the memory instruction. Hence the phase is different from $\mathrm{start}$, and both deterministic-part programs replace the memory instruction by the same return instruction, regardless of the answer parameter (`MARM.detPart_mem`). Their transitions therefore agree in this case as well, which establishes the required equality.

**Key facts.** `Complexity.LogProg.armProg_mdetPart_call`, `Complexity.LogProg.ctr_congr`, `Complexity.LogProg.MARM.detPart_det`, `Complexity.LogProg.MARM.detPart_mem`.
