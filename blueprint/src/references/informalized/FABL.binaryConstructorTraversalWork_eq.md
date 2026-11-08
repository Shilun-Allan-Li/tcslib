<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryConstructorTraversalWork_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Traversal Work for a List

**Claim.** For any step cost and finite list of items, the total traversal work is the list length multiplied by the step cost.

**Proof.** Proceed by induction on the list. The empty list has zero traversal work and length zero, so the formula holds. For a list with head and tail, the work is the step cost plus the work on the tail. By induction the latter is the tail length times the step cost; since the list length is one more than the tail length, the result follows from the distributive law for natural-number multiplication.
