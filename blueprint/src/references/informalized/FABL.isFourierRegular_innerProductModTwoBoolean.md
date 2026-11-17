<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/RegularityComparisons.lean :: FABL.isFourierRegular_innerProductModTwoBoolean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mod-Two Inner Product Regularity

**Claim.** For every natural number $m$, the Boolean function given by the Mod-Two inner product has every nonempty-set Fourier coefficient bounded in absolute value by $2^{-m}$.

**Proof.** Fix a coordinate set $S$. The exact coefficient formula for this function says that its Fourier coefficient at $S$ has absolute value $(2^m)^{-1}$. Since this is precisely the regularity threshold, the required bound follows for every nonempty $S$.

**Key facts.** `FABL.abs_fourierCoeff_innerProductModTwoBoolean`.
