<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.stableInfluence_leadingCoordinateTimes_majority_odd_eq_noiseStability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Stable Influence Identity

**Claim.** For every natural number $m$ and $0<\delta<1$, the stable influence at parameter $1-\delta$ of the leading-coordinate product with majority on $2m+1$ coordinates equals the noise stability of that majority at the same parameter.

**Proof.** Apply the identity relating the stable influence of a function obtained by multiplying a new leading coordinate by $g$ to the stability curve of $g$ (\texttt{stableInfluence_leadingCoordinateTimes_eq_stabilityCurve}). This identifies the left side with the stability curve of majority on $2m+1$ coordinates, evaluated at $1-\delta$. The hypotheses on $\delta$ imply $-1\le 1-\delta\le 1$, so the stability-curve/noise-stability identity (\texttt{stabilityCurve_eq_noiseStability}) applies and gives the desired equality.

**Key facts.** `FABL.stableInfluence_leadingCoordinateTimes_eq_stabilityCurve`, `FABL.stabilityCurve_eq_noiseStability`.
