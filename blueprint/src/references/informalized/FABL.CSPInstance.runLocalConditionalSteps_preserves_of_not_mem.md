<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.runLocalConditionalSteps_preserves_of_not_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unvisited Variables Are Preserved

**Claim.** Running local conditional steps through a list leaves the law and assigned label of every variable absent from that list unchanged.

**Proof.** Induct on the list. With no steps, the state is unchanged. For a list with head $v$ and tail $L$, absence of the target variable $x$ from the full list means both $x\ne v$ and $x\notin L$. The step at $v$ changes only the marginal and assignment at $v$, so it leaves both coordinates at $x$ unchanged. By induction, running the remaining steps through $L$ also preserves both coordinates at $x$. Combining these equalities proves the result.
