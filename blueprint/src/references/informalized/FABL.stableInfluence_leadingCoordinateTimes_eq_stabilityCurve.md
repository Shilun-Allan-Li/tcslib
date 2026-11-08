<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.stableInfluence_leadingCoordinateTimes_eq_stabilityCurve -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence Equals Stability Curve

**Claim.** For a Boolean function $g$ and any real $\rho$, the stable influence in coordinate $0$ of the leading-coordinate product function, converted to real values, equals the stability curve of $g$'s real-valued version.

**Proof.** Index the stable-influence sum by frequency sets containing $0$. Each such set has the form $\{0\}\cup\operatorname{tailFrequency}(S)$ for a unique frequency set $S$ on the original cube: the inverse is obtained by taking the frequency tail, and reinserting $0$ recovers the original set (`insert_zero_tailFrequency_frequencyTail_eq`). The tail-frequency set excludes $0$ (`zero_notMem_tailFrequency`) and preserves cardinality (`card_tailFrequency`), so the enlarged set has size $|S|+1$, making its stable-influence exponent equal to $|S|$. The Fourier coefficient of the enlarged function at that set equals the original coefficient at $S$ (`fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency`). Consequently corresponding summands agree, and this bijection identifies the entire stable-influence sum with the stability-curve sum.

**Key facts.** `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`, `FABL.fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency`, `FABL.insert_zero_tailFrequency_frequencyTail_eq`.
