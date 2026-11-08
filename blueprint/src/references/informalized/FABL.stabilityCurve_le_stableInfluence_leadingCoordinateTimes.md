<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.stabilityCurve_le_stableInfluence_leadingCoordinateTimes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stability Bounded by Stable Influence

**Claim.** For a Boolean function $g$ on the $n$-dimensional sign cube and $\rho\in[0,1]$, the stability curve of its real-valued version is at most the stable influence in coordinate $0$ of the function obtained by multiplying the leading coordinate by $g$ on the remaining coordinates.

**Proof.** For each frequency set $S$ on the original cube, associate the frequency set $T=\{0\}\cup\operatorname{tailFrequency}(S)$ on the enlarged cube. The tail-frequency map preserves cardinality (`card_tailFrequency`), and its image contains no leading coordinate (`zero_notMem_tailFrequency`), so $|T|-1=|S|$. The Fourier coefficient at $T$ of the enlarged function equals the Fourier coefficient at $S$ of $g$ (`fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency`). Thus the stability-curve summand indexed by $S$ equals the stable-influence summand indexed by its image $T$. The map is injective: erase $0$ from equal image sets to recover equal tail-frequency sets, then use injectivity of the coordinate embedding. Therefore the stability curve is exactly the sum over these image sets. They form a subset of all frequency sets containing $0$. Every omitted summand is nonnegative, since $\rho\geq0$ and it is a nonnegative power of $\rho$ times a square. Extending the sum to all sets containing $0$ can only increase it, proving the inequality.

**Key facts.** `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`, `FABL.fourierCoeff_leadingCoordinateTimes_insert_zero_tailFrequency`.
