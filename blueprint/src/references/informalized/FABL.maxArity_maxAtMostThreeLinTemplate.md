<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.maxArity_maxAtMostThreeLinTemplate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Arity of the Linear Template

**Claim.** The maximum arity of the maximum-at-most-three linear constraint template is $3$.

**Proof.** For the upper bound, every predicate has an arity index in $\mathrm{Fin}(4)$, so its value is at most $3$. Hence the supremum of all predicate arities is at most $3$. For the reverse inequality, choose the predicate whose arity index is $3$ and whose right-hand side is $0$. It belongs to the template's predicate family, and its arity is $3$, so the supremum is at least $3$. Together these inequalities give the result.
