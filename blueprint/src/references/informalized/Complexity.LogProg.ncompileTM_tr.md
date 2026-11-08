<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ncompileTM_tr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Away from Choice

**Claim.** At any compiled state where $A$ offers no nondeterministic choice, the compiled machine's transition under choice bit $b$ agrees with the deterministic compilation in which each choice instruction is replaced by the return value $\beta$.

**Proof.** Because the choice-target function returns no targets at $q$, the compiled machine uses its deterministic transition construction there. The proof compares this construction with the one for the deterministic program obtained from $A$ by replacing choices with returns. First, these two programs have the same call behavior (`Complexity.LogProg.armProg_detPart_call`), so the call-handling portions of the compiled transition agree (`Complexity.LogProg.ctr_congr`) once their ordinary program transitions agree. For an ordinary instruction $A(l)$ that is deterministic, both deterministic replacements retain that instruction (`Complexity.LogProg.NARM.detPart_det`), and therefore their transitions agree. If $A(l)$ is a choice instruction, the absence of choice targets at $q$ rules out the initial phase at that label: choices would be exposed as targets there. At every other phase, the compiled instruction transition is the same for either replacement, since the two replacements are return instructions and the noninitial-phase transition for a return is the same in both cases. Thus the ordinary transitions agree as well, proving the equality for every input symbol and work-tape reading, and hence the claimed transition equality.

**Key facts.** `Complexity.LogProg.armProg_detPart_call`, `Complexity.LogProg.ctr_congr`, `Complexity.LogProg.NARM.detPart_det`, `Complexity.LogProg.NARM.detPart_choose`.
