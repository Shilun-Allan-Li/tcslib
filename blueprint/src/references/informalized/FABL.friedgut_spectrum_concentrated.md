<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.friedgut_spectrum_concentrated -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concentration on the Friedgut Family

**Claim.** For a Boolean function with positive parameter and positive total influence, its Fourier spectrum is concentrated to error $2\epsilon$ on the family of sets contained in the Friedgut coordinates whose cardinality is at most the Friedgut degree.

**Proof.** First, the degree-tail concentration result says that the Fourier spectrum is concentrated to error $\epsilon$ on sets of size at most the Friedgut degree (`spectrum_concentrated_up_to_friedgutDegree`). Apply the small-family consequence of Theorem 9.28 with this degree, the assumed positive parameter and influence, and that degree-tail bound. It gives concentration to error $2\epsilon$ on the family whose members lie in the coordinates selected by the threshold and have size at most the degree. Unfolding the definition of the Friedgut coordinates identifies that family with the one in the claim.

**Key facts.** `FABL.spectrum_concentrated_up_to_friedgutDegree`, `FABL.theorem9_28_small_spectrum_concentrated`.
