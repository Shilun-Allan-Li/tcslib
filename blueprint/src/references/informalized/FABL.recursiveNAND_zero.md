<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.recursiveNAND_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recursive NAND at Depth Zero

**Claim.** For every sign vector $x$ with $2^0$ coordinates, the depth-zero recursive NAND is the value of $x$ at its sole coordinate.

**Proof.** At depth zero, the recursive function is defined to return the coordinate $x(0)$. The claimed equality is therefore the base clause of its definition.
