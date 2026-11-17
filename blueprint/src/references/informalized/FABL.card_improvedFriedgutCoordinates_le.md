<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.card_improvedFriedgutCoordinates_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Improved Friedgut coordinate bound

**Claim.** With $\epsilon>0$, $0<\eta\le1$, and positive total influence $I$, the number of coordinates whose influence reaches the stated improved Friedgut threshold is at most $I^{2+\eta}\epsilon^{-(1+\eta)}(2/\eta+1)^{2k}$.

**Proof.** Let $\tau$ be the improved Friedgut threshold. It is positive (`improvedFriedgutThreshold_pos`), so the number of coordinates with influence at least $\tau$ is at most $I/\tau$ (`card_influentialCoordinates_le_div`). The threshold is bounded below by $(\epsilon/I)^{1+\eta}\rho^{2k}$, where $\rho=\eta/(2+\eta)$ (`improvedFriedgutThreshold_lower`); positivity of $\rho$ follows from `improvedFriedgutRho_pos`. Since $I\ge0$, replacing the denominator by this positive lower bound gives an upper bound for $I/\tau$. The resulting quotient is exactly the claimed expression, by the denominator identity `improvedFriedgut_bookDenominator_identity`.

**Key facts.** `FABL.improvedFriedgutThreshold_pos`, `FABL.improvedFriedgutThreshold_lower`, `FABL.improvedFriedgutRho_pos`, `FABL.card_influentialCoordinates_le_div`, `FABL.totalInfluence_nonneg`, `FABL.improvedFriedgut_bookDenominator_identity`.
