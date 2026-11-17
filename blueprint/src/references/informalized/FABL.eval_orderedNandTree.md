<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.eval_orderedNandTree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Ordered NAND Tree Evaluation

**Claim.** For disjoint coordinate sets and sign-output decision trees on those sets, the ordered composition evaluates to $1$ exactly when both tree outputs are $-1$, and to $-1$ otherwise.

**Proof.** The ordered composition first runs the tree on the first coordinate set. At each resulting output, it continues with the second tree through the NAND continuation construction. The evaluation rule for that continuation says its output is $1$ exactly when the first tree's output and the second tree's output are both $-1$, and is $-1$ otherwise. Thus the composed tree evaluates to the NAND of the two tree outputs. The disjointness condition is part of the construction that makes this ordered composition available.
