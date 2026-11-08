<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/Mult.lean :: Complexity.mult_preconditions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Instruction side conditions

**Claim.** For every input string, state, register assignment, and recorded-answer choice, the corresponding configuration satisfies the multiplication program's instruction side conditions: compared registers are distinct and oracle-call register lists have no repetitions.

**Proof.** Inspect the program state by state. For an ordinary state, unfolding the instruction and side-condition definitions reduces the claim to checking that either the instruction has no relevant side condition or its fixed register arguments satisfy it. The finite cases are discharged directly. In a copy state with the non-bumping flag, the only comparison is between the two registers specified by the copy table; those are distinct for every table entry, as a finite check confirms. With the bumping flag, the instruction is an increment, so there is no comparison condition to check. The parameterized canonical-test cases reduce to the same direct checks after splitting on the field index. In the end-down, count-down, next-$b$, and next-$a$ states, both possibilities for the Boolean parameter yield instructions with no additional condition. Hence every state satisfies the required side conditions, independently of the registers and recorded answer.
