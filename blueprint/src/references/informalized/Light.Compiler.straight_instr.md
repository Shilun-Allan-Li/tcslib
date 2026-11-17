<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Expressions.lean :: Light.Compiler.straight_instr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Straightness of arithmetic instructions

**Claim.** For every operation chosen from addition, subtraction, and multiplication, and every three integer locations $i,j,k$, the corresponding instruction with destination $i$ and operands $j,k$ is straight.

**Proof.** There are three possibilities for the operation. If it is addition, the corresponding instruction is an addition; if it is subtraction, it is a subtraction; and if it is multiplication, it is a multiplication. Each of these instruction forms is straight by definition, for any choice of locations.
