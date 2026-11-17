<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.restrict_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Duality Under Restriction

**Claim.** Restricting the Boolean dual of $f$ according to $\rho$ gives the binary Boolean dual of the restriction of $f$ according to the coordinatewise negation of $\rho$.

**Proof.** Evaluate both sides at an arbitrary binary input $x$ and unfold restriction and both dual operations. Each side is the negative of $f$ evaluated at a completed sign-cube input. The left uses the coordinatewise negation of the completion under $\rho$; the right completes the coordinatewise complement of $x$ under the negated assignment. These completed inputs agree by `complete_negateAssignment`, so the outputs agree for every $x$, proving equality of the functions.

**Key facts.** `FABL.CoordRestriction.complete_negateAssignment`.
