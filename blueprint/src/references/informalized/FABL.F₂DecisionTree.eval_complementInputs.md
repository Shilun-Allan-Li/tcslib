<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.F₂DecisionTree.eval_complementInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation under Input Complementation

**Claim.** Interchanging the two branches at every query and evaluating at $x$ gives the same output as evaluating the original tree at the coordinatewise complement of $x$.

**Proof.** Proceed by induction on the tree. At a leaf both evaluations return its stored value. At a query of coordinate $i$, split into the two possible values of $x_i$. If $x_i=0$, the complemented input has value $1$ there, so the original tree follows its one-child; the tree with branches interchanged follows its zero-child, and the induction hypothesis for that child identifies the outputs. If $x_i=1$, the complemented input has value $0$, and the same reasoning with the zero-child and one-child exchanged proves the claim.
