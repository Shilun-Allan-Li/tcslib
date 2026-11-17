<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.expect_satisfiedIndicator_maxE3Lin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected satisfaction of a three-variable constraint

**Claim.** For a constraint on three distinct variables whose sum in $\mathbb{F}_2$ must equal a specified right-hand side, the expected satisfaction indicator under a uniform random assignment is $1/2$.

**Proof.** Split each assignment into its values on the constraint's three variables and its values on all remaining variables. The scope-splitting equivalence preserves the uniform expectation, and its first component is exactly the assignment restricted to the scope (the scope-coordinate identity, `cspScopeSplitEquiv_fst_apply`). Averaging first over the remaining variables changes nothing, since the indicator depends only on the three scoped values. The expected indicator for the three-variable predicate is $1/2$ (`expect_e3LinPredicate`), giving the result.

**Key facts.** `FABL.cspScopeSplitEquiv_fst_apply`, `FABL.expect_e3LinPredicate`.
