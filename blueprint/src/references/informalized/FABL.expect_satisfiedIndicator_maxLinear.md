<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.expect_satisfiedIndicator_maxLinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected satisfaction of a linear constraint

**Claim.** For a constraint on a nonempty set of distinct variables whose sum in $\mathbb{F}_2$ must equal a specified right-hand side, the expected satisfaction indicator under a uniform random assignment is $1/2$.

**Proof.** Decompose a uniform assignment into its values on the constraint's scope and on the variables outside that scope. The scope-splitting equivalence preserves the expectation, and its first component gives precisely the values assigned to the scoped variables (`maxLinearScopeSplitEquiv_fst_apply`). The satisfaction indicator depends only on those values, so averaging over the outside values leaves it unchanged. The expected indicator for the linear predicate on its scope is $1/2$ (`expect_maxLinearPredicate`).

**Key facts.** `FABL.maxLinearScopeSplitEquiv_fst_apply`, `FABL.expect_maxLinearPredicate`.
