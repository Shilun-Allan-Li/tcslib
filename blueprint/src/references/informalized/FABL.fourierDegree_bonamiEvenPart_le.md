<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.fourierDegree_bonamiEvenPart_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the Bonami even part

**Claim.** If a function on the $(n+1)$-dimensional Boolean cube has Fourier degree at most $k$, then the average of its two first-coordinate slices has Fourier degree at most $k$.

**Proof.** Use the characterization of degree at most $k$ by vanishing of every Fourier coefficient indexed by a set of size greater than $k$ (`FABL.fourierDegree_le_iff`). For such a set $S$ on the $n$ remaining coordinates, the coefficient of the averaged-slice function equals the coefficient of the original function at the corresponding tail-frequency set (`FABL.fourierCoeff_bonamiEvenPart`). That set has the same cardinality as $S$ (`FABL.card_tailFrequency`), so its size is still greater than $k$. The assumed degree bound forces this coefficient to vanish, proving the claimed degree bound.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_bonamiEvenPart`, `FABL.card_tailFrequency`.
