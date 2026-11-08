<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.CNFFormula.switchAndOr_truncateWidth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Commutes with Width Truncation

**Claim.** For a CNF formula, switching its clauses to DNF terms commutes with retaining only clauses or terms of width at most a given bound.

**Proof.** Both operations act on the same list of stored objects: switching uses the clause list as the DNF term list, and truncation filters that list by the width bound. Thus either order produces the identical filtered list, so the formulas are equal by their definitions.
