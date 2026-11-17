<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CoordRestriction.restrictSign_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Under Sign Restriction

**Claim.** Restricting the Boolean dual of $f$ using $\rho$ gives the Boolean dual of the restriction of $f$ using the coordinatewise negation of $\rho$.

**Proof.** Evaluate both sides at an arbitrary sign-cube input $x$ and unfold restriction and Boolean duality. On the left, the value is the negative of $f$ evaluated at the coordinatewise negation of the completion determined by $\rho$ and $x$. On the right, it is the negative of $f$ evaluated at the completion determined by the negated restriction assignment and the coordinatewise negation of $x$. These two inputs to $f$ agree by the completion identity for negated assignments (`completeSign_negateAssignment`). Hence the values agree for every $x$, so the functions are equal.

**Key facts.** `FABL.CoordRestriction.completeSign_negateAssignment`.
