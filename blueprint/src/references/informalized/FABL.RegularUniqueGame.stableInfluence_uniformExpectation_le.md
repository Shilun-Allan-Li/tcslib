<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.stableInfluence_uniformExpectation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence of a Uniform Function Average

**Claim.** For $\rho\in[0,1]$, the stable influence of a finite nonempty uniform average of functions at any coordinate is at most the uniform average of their stable influences there.

**Proof.** Write the stable influence as a sum over subsets containing the chosen coordinate. For each subset, its weight is $\rho^{|S|-1}$, which is nonnegative because $\rho\geq0$. Encode these weights in a nonnegative coefficient function on all subsets, assigning coefficient zero to subsets that do not contain the coordinate. Stable influence is then the corresponding Fourier-square functional. The convexity inequality for this functional under uniform averaging (`fourierSquareFunctional_uniformExpectation_le`) bounds its value on the average function by the average of its values on the individual functions. With the chosen coefficients, this is precisely the desired stable-influence inequality.

**Key facts.** `FABL.fourierSquareFunctional_uniformExpectation_le`.
