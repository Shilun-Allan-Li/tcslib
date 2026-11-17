<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPTemplate.maxArity_eq_of_forall_arity_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Maximum Arity for Constant Arity

**Claim.** If the predicate family is nonempty and every predicate has arity $r$, then its maximum arity is $r$.

**Proof.** Every predicate has arity $r$, so every term in the supremum defining the maximum arity is at most $r$. Thus the maximum arity is at most $r$. Since the family is nonempty, choose a predicate in it. Its arity is $r$, and the supremum is at least each member's arity; hence the maximum arity is at least $r$. The two inequalities give equality.
