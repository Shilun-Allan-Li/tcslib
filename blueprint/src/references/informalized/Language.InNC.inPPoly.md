<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/NCAC.lean :: Language.InNC.inPPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NC Circuits Have Polynomial Size

**Claim.** If a language has an NC circuit family with fan-in at most two, polynomial size, and the stated depth bound, then it has a well-formed fan-in-two circuit family of polynomial size.

**Proof.** Take the family and its fan-in-two and polynomial-size properties from the NC hypothesis; the depth bound is not needed for this conclusion. The characterization of polynomial size in this circuit model (`Language.inPPoly_iff`) says precisely that a family with these properties witnesses membership in the polynomial-size class. Applying that characterization gives the claim.

**Key facts.** `Language.inPPoly_iff`.
