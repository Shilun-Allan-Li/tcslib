<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mop_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of Memory Selection

**Claim.** If the memory-operation selector returns instruction $i$ at compiled state $q$, then $q$ is the program-running state at some $l$ in the start phase, $A$ assigns $i$ at $l$, and $i$ is a memory instruction.

**Proof.** Unpack the selector's definition. It can return an instruction only when the state has the form of a program-running state at $l$ with phase $	ext{start}$; all other compiled-state constructors return no instruction. In that case, the selector returns $A(l)$ precisely when the phase is start and the assigned instruction is a memory instruction. Equality of the returned option with the given singleton identifies $i$ with $A(l)$, and the condition for selecting it supplies that it is a memory instruction.
