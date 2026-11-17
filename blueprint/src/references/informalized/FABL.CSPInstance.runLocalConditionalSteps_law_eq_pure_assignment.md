<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.runLocalConditionalSteps_law_eq_pure_assignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Visited Variables Become Deterministic

**Claim.** After the local conditional steps are run through a list of variables, each variable in that list has a law concentrated at its assigned label in the resulting state.

**Proof.** Induct on the list. The empty list contains no variable, so the claim is vacuous. For a list with head $v$ and tail $L$, consider the target variable $x$. If $x$ occurs in $L$, apply the induction hypothesis to the run on $L$ starting from the state produced by the step at $v$.

Otherwise, since $x$ occurs in the full list, it must equal $v$. The subsequent run through $L$ preserves both the law and assigned label at $v$, because $v$ is absent from $L$ (`runLocalConditionalSteps_preserves_of_not_mem`). Immediately after the step at $v$, its law is the point mass at the label chosen by that step, and its assignment is updated to that same label. Preservation through the tail therefore gives the claimed equality in the final state.

**Key facts.** `FABL.CSPInstance.runLocalConditionalSteps_preserves_of_not_mem`.
