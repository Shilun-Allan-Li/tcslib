<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SiegenthalerSharpness.lean :: FABL.booleanFunctionF₂Decoding_anfMonomial_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinate Dependence of a Decoded Monomial

**Claim.** The sign-valued function obtained by decoding the monomial indexed by $S$ depends only on the coordinates in $S$.

**Proof.** Take two sign vectors that agree on every coordinate in $S$. Under the coordinatewise inverse bit-to-sign correspondence, their binary vectors also agree on each such coordinate, because applying the same function to equal signs preserves equality. The monomial is a product of precisely those coordinates indexed by $S$, so the two monomial values coincide. Applying the sign encoding to these equal values gives equal decoded function values.
