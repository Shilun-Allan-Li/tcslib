<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.card_improvedFriedgutCoordinates_le_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# General improved Friedgut coordinate bound

**Claim.** For positive $\epsilon,\eta$ and positive total influence $I$, the number of coordinates whose influence reaches the stated general improved Friedgut threshold is at most $I^{2+\eta}\epsilon^{-(1+\eta)}(2/\eta+1)^{(1+\eta)k}$.

**Proof.** The improved threshold is positive (`improvedFriedgutThreshold_pos`), so the number of coordinates whose influence reaches it is at most $I$ divided by that threshold (`card_influentialCoordinates_le_div`). The resulting quotient equals the claimed general bound by the identity `improvedFriedgut_generalDenominator_identity`.

**Key facts.** `FABL.improvedFriedgutThreshold_pos`, `FABL.card_influentialCoordinates_le_div`, `FABL.improvedFriedgut_generalDenominator_identity`.
