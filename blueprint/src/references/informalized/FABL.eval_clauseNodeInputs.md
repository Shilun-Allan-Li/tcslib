<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.eval_clauseNodeInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Node Evaluation

**Claim.** For an input sign assignment, the disjunction over the selected first-layer nodes equals the clause evaluation on the assignment of block parity outputs.

**Proof.** First, the clause evaluates to $-1$ exactly when some literal has its required sign at its indexed block: this follows by expanding the clause evaluation and the literal evaluation. The disjunction over the selected nodes evaluates to $-1$ exactly when one of its inputs evaluates to $-1$ (the disjunction characterization, `FABL.CircuitGate.evalFinset_or_eq_neg_one_iff`). If such a node is selected, its defining data give a literal whose index is the node's block and whose required sign is the node's parity output. The first-layer evaluation characterization (`FABL.eval_blockFirstLayer`) says that the node evaluates to $-1$ precisely when its encoded block assignment is the input restricted to that block. Thus its parity output is the block output, so the corresponding literal is satisfied by the block-output assignment. Conversely, if a literal is satisfied by that assignment, choose the node encoded by its block index and the input restricted to that block. This node is selected, has the required parity output, and evaluates to $-1$ by the same first-layer characterization. Hence the disjunction is $-1$ exactly when the clause is $-1$. Since both values are signs, if neither is $-1$ then both are $1$ (`FABL.CNFFormula.sign_eq_of_ne_neg`), proving equality in all cases.

**Key facts.** `FABL.CircuitGate.evalFinset_or_eq_neg_one_iff`, `FABL.eval_blockFirstLayer`, `FABL.CNFFormula.sign_eq_of_ne_neg`.
