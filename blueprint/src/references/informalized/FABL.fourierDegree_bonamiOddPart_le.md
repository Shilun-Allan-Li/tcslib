<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.fourierDegree_bonamiOddPart_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the odd coordinate part

**Claim.** If a function on the $(n+1)$-dimensional Boolean cube has Fourier degree at most $k+1$, then half the difference of its two first-coordinate slices has Fourier degree at most $k$.

**Proof.** Apply the coefficient characterization of degree at most $k$ (`FABL.fourierDegree_le_iff`). For a set $S$ on the remaining coordinates with $|S|>k$, the Fourier coefficient of the odd part equals the coefficient of the original function at the set formed by adjoining the first coordinate to the tail-frequency set (`FABL.fourierCoeff_bonamiOddPart`). The first coordinate is absent from that tail-frequency set (`FABL.zero_notMem_tailFrequency`), and the tail-frequency set has size $|S|$ (`FABL.card_tailFrequency`); adjoining the first coordinate therefore gives a set of size $|S|+1>k+1$. The assumed degree bound for the original function makes this coefficient zero. Thus every coefficient of the odd part above degree $k$ vanishes.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.fourierCoeff_bonamiOddPart`, `FABL.zero_notMem_tailFrequency`, `FABL.card_tailFrequency`.
