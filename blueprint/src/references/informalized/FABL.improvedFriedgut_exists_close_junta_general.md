<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgut_exists_close_junta_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# General close junta existence

**Claim.** Under the stated assumptions, there exist a coordinate set and a Boolean function satisfying the general junta size bound, Fourier concentration bound, junta dependence, and approximation bound.

**Proof.** Choose $J$ to be the coordinates whose pivotal probabilities meet the improved threshold, and let $g$ be the coordinate junta approximation on $J$. The general coordinate-count estimate (`card_improvedFriedgutCoordinates_le_general`) bounds $|J|$ by the stated general junta size term. The small-spectrum concentration result (`improvedFriedgut_small_spectrum_concentrated`) gives Fourier weight at most $2\epsilon$ outside sets contained in $J$ of size at most $k$. The approximation is a $|J|$-junta (`coordinateJuntaApproximation_isKJunta`), and its relative Hamming distance from $f$ is at most $\epsilon$ (`improvedFriedgut_coordinateJunta_close`). Thus this choice satisfies all four required properties.

**Key facts.** `FABL.card_improvedFriedgutCoordinates_le_general`, `FABL.improvedFriedgut_small_spectrum_concentrated`, `FABL.coordinateJuntaApproximation_isKJunta`, `FABL.improvedFriedgut_coordinateJunta_close`.
