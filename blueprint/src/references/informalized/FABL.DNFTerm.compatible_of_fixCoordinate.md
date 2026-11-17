<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFTerm.compatible_of_fixCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility after freeing a coordinate

**Claim.** If coordinate $i$ is free under a restriction and the term is compatible after that coordinate is fixed to the state determined by $s$, then the term is compatible under the original restriction.

**Proof.** Take an assignment $x$ witnessing compatibility after fixing coordinate $i$. Replace its bit at $i$ by the binary encoding of $s$. The coordinate-completion identity for fixing a previously free coordinate states that completing the fixed restriction with $x$ equals completing the original restriction with this updated assignment (`CoordRestriction.complete_fixCoordinate_of_free`). Hence the updated assignment produces exactly the already-satisfying sign vector, so it witnesses compatibility under the original restriction.

**Key facts.** `FABL.CoordRestriction.complete_fixCoordinate_of_free`.
