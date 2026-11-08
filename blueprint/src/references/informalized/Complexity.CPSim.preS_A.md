<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/CounterProgSim.lean :: Complexity.CPSim.preS_A -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preconditions of the Compiled Machine

**Claim.** For a valid plain input, every configuration of the compiled machine satisfies the required preconditions for its current instruction: register comparisons use distinct registers, input-word comparisons use valid inputs, and oracle calls have no repeated argument registers.

**Proof.** If the configuration has no current label, the precondition holds by definition. Otherwise inspect its compiled label. At a simulation label, the underlying counter instruction determines the compiled instruction: output comparisons and input reads use the assumed valid plain input where needed, and the other instruction forms impose no additional condition. At a print-loop label, the only possible register comparison is between the temporary register and an original register; these are distinct by the fact that the temporary register differs from every original one (`rT_ne_rg`). At read-processing labels, the compiled instruction is either an oracle call with the singleton argument list containing the position register, which has no repetitions, or an instruction with no precondition. All remaining compiled labels likewise produce instructions whose precondition is automatic or whose input comparison is justified by validity of the given input.

**Key facts.** `Complexity.CPSim.rT_ne_rg`.
