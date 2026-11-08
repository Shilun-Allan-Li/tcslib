<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.maxArity_maxE3SatTemplate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Arity of the Three-Variable Satisfiability Template

**Claim.** The maximum arity of the three-variable satisfiability constraint template is $3$.

**Proof.** The template has at least one predicate, and every predicate has arity $3$. The fact that a nonempty template whose predicates all have arity $r$ has maximum arity $r$ (`CSPTemplate.maxArity_eq_of_forall_arity_eq`) applies with $r=3$, giving the result.

**Key facts.** `FABL.CSPTemplate.maxArity_eq_of_forall_arity_eq`.
