<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.cspScopeSplitEquiv_fst_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constraint Scope Restriction

**Claim.** For an assignment to the variables, the first component of its scope/off-scope decomposition, evaluated at a position in the ordered scope, is the assignment's value at the variable in that position.

**Proof.** The decomposition first restricts the assignment to variables in the scope, then reindexes that restriction by the scope's positions. At position $i$, the reindexing selects the variable $c.scope(i)$, so the resulting value is exactly $assignment(c.scope(i))$.
