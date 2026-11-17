<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.preS_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Search-Machine Preconditions

**Claim.** For every bit string $x$ and every configuration of the deterministic part of the search machine with parameter $K_0$, the precondition defining admissible comparisons, input comparisons, and oracle calls holds.

**Proof.** If the control component of the configuration is halted, the precondition holds by definition. Otherwise inspect the current label and the instruction produced there by the deterministic part of the search machine. At the input-code query label, the only register comparison is between the source register and a phase-radius register; these are distinct by the radius-register separation fact (`rad_ne_U`). At the step-query label, the three phase cases give pairwise distinct registers among source, target, and radius, so the comparison and call requirements hold. The labels that clear registers, advance loop counters, or perform copy, move, and shift operations introduce no additional precondition. For the memory-access labels, the outward walk, read-or-mark operation, and return walk likewise produce only instructions whose preconditions are automatic. The remaining labels are checked directly from the machine's instruction table; all their comparisons use distinct registers and their calls have lists of distinct argument registers. Hence the precondition holds in every configuration.

**Key facts.** `Complexity.LogProg.ExpBFS.rad_ne_U`.
