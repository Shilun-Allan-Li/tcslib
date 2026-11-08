<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.eval_reindex -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation after coordinate reindexing

**Claim.** Reindexing a finite decision tree along an embedding $e$ and evaluating it at $x$ gives the same output as evaluating the original tree at the input $i\mapsto x_{e(i)}$.

**Proof.** Proceed by induction on the tree. At a leaf, the evaluations agree. At a query of coordinate $i$, the reindexed tree queries $e(i)$, so it selects the child indexed by $x_{e(i)}$. That child is the reindexing of the corresponding original child, with its available coordinates identified using the equality between the image of an erased set and the image set with $e(i)$ removed. Replacing the available-set index along this equality preserves evaluation (\texttt{FABL.FiniteDecisionTree.eval\_castAvailable}). The induction hypothesis for that child gives the result.

**Key facts.** `FABL.FiniteDecisionTree.eval_castAvailable`.
