<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_exists_close_junta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existence of a close junta

**Claim.** Under the hypotheses, there are a coordinate set and a Boolean function with the asserted size, Fourier concentration, junta dependence, and approximation bounds.

**Proof.** Choose $J$ to be the coordinates whose pivotal probabilities meet the improved threshold, and let $g$ be the coordinate junta approximation obtained by conditioning on $J$. The coordinate-count estimate (`card_improvedFriedgutCoordinates_le`) gives the required upper bound on $|J|$. The small-spectrum concentration result (`improvedFriedgut_small_spectrum_concentrated`) gives Fourier weight at most $2\epsilon$ outside the sets contained in $J$ and of size at most $k$. The coordinate approximation is a $|J|$-junta (`coordinateJuntaApproximation_isKJunta`), and its relative Hamming distance from $f$ is at most $\epsilon$ (`improvedFriedgut_coordinateJunta_close`). These four properties hold for the chosen pair $(J,g)$, proving existence.

**Key facts.** `FABL.card_improvedFriedgutCoordinates_le`, `FABL.improvedFriedgut_small_spectrum_concentrated`, `FABL.coordinateJuntaApproximation_isKJunta`, `FABL.improvedFriedgut_coordinateJunta_close`.
