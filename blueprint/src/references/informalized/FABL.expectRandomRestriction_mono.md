<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.expectRandomRestriction_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of restriction expectation

**Claim.** When $0\leq\delta\leq1$, pointwise domination of two functions on every restriction implies the same ordering of their expected random restrictions.

**Proof.** Expand the expectation as a sum over free-coordinate sets. For each set, averaging the pointwise inequalities over the fixed signs preserves the inequality, since a uniform expectation is a finite average. The coefficient multiplying that average is nonnegative: this is the nonnegativity of the random-subset weight (`deltaRandomSubsetWeight_nonneg`), which follows under the stated bounds on $\delta$. Multiplying preserves the inequality, and summing these inequalities over all free-coordinate sets proves the claim.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`.
