<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMReach.lean :: Complexity.LogProg.astep_cases -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Possible Outcomes of One Abstract Step

**Claim.** From an active configuration with state $l$, registers $v$, and stored answer $res$, one abstract step either produces an active configuration with the same stored answer, or halts with the same registers and some Boolean answer.

**Proof.** Split on the instruction assigned to $l$. A return instruction halts with its specified Boolean answer. For either validation instruction, split on whether the input encoding is valid: a valid encoding continues with the same registers and stored answer, while an invalid one halts with a negative answer. Every other instruction continues at an active state, changing registers only as prescribed by the instruction and retaining the stored answer. These cases give the two stated forms.
