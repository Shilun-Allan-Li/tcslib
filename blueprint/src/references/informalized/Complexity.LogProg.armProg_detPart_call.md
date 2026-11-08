<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.armProg_detPart_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice Replacement Preserves Calls

**Claim.** Replacing every choice instruction of $A$ by a return of either Boolean value yields compiled register programs with identical call maps.

**Proof.** Fix a state-phase pair $(l,ph)$. If $A(l)$ is deterministic, both replacements retain that same instruction, so their call specifications at phase $ph$ agree. If $A(l)$ is a choice, either replacement produces a return instruction (with its respective Boolean value). A return is not a call instruction, so its call specification is empty at every phase; hence the two call specifications again agree. Since this holds at each state-phase pair, the call maps are equal.

**Key facts.** `Complexity.LogProg.NARM.detPart_det`, `Complexity.LogProg.NARM.detPart_choose`.
