<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Friedgut.lean :: FABL.card_friedgutCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Friedgut coordinate bound

**Claim.** For a Boolean function with positive total influence and positive $\varepsilon$, the number of its Friedgut coordinates is at most $I[f]^3\varepsilon^{-2}9^{\mathrm{friedgutDegree}(f,\varepsilon)}$, where $I[f]$ denotes its total influence.

**Proof.** Apply the bound on influential coordinates (card_theorem9_28_influentialCoordinates_le) with threshold parameter $\varepsilon$ and degree parameter $k=\mathrm{friedgutDegree}(f,\varepsilon)$. The Friedgut coordinate set is precisely the influential-coordinate set at that threshold and degree. Substituting this definition into the bound gives the claimed inequality.

**Key facts.** `FABL.card_theorem9_28_influentialCoordinates_le`.
