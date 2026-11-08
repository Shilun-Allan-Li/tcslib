<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.lowDegreeOutsideInfluentialMass_improvedThreshold_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Mass Outside Influential Coordinates

**Claim.** For a Boolean function with positive total influence, the sum of squared Fourier coefficients on sets of size at most $k$ that are not contained in the coordinates of influence at least the improved threshold is at most $\epsilon$.

**Proof.** Let $\tau$ be the improved threshold. The low-degree mass estimate bounds the mass outside the influential coordinates at threshold $\tau$ by $\rho(\eta)^{-k}\tau^{1/(1+\eta)}I(f)$ (`lowDegreeOutsideInfluentialMass_le_improved`). The threshold is positive (`improvedFriedgutThreshold_pos`), so this estimate applies. By the threshold power identity (`improvedFriedgutThreshold_rpow`), its middle factor is $\epsilon I(f)^{-1}\rho(\eta)^k$. Since $\eta>0$, $\rho(\eta)>0$ (`improvedFriedgutRho_pos`), and since $I(f)>0$, both reciprocal cancellations are valid. Substituting and canceling yields exactly $\epsilon$, proving the desired bound.

**Key facts.** `FABL.improvedFriedgutRho_pos`, `FABL.improvedFriedgutThreshold_pos`, `FABL.lowDegreeOutsideInfluentialMass_le_improved`, `FABL.improvedFriedgutThreshold_rpow`.
