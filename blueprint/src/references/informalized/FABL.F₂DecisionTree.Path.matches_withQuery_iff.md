<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/DecisionTrees.lean :: FABL.F₂DecisionTree.Path.matches_withQuery_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching after an additional query

**Claim.** If coordinate $i$ is not in the path's support, the path obtained by assigning $b$ at $i$ matches $x$ exactly when the original path matches $x$ and $x_i=b$.

**Proof.** First, absence of $i$ from the support means its original assignment is undefined (`assignment_eq_none_of_not_mem_support`). Suppose the extended path matches $x$. At coordinate $i$, the new assignment is $b$, so matching forces $x_i=b$. At any other coordinate, the update leaves the assignment unchanged, so every original requirement is satisfied. Conversely, suppose the original path matches $x$ and $x_i=b$. At coordinate $i$, the extended requirement is exactly this equality; at every other coordinate the assignment is unchanged, and the original matching condition supplies agreement. Thus the extended path matches precisely under the two stated conditions.

**Key facts.** `FABL.F₂DecisionTree.Path.assignment_eq_none_of_not_mem_support`.
