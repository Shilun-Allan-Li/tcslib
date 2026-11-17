<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.influence_uniformExpectation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence of an Average of Functions

**Claim.** For a finite nonempty family of real-valued functions on the Boolean cube, the influence of a coordinate in their pointwise average is at most the average of their influences in that coordinate.

**Proof.** Use the convexity inequality for stable influence under finite uniform averaging at parameter $1$; the parameter lies in $[0,1]$. This bounds stable influence of the pointwise average by the average of the stable influences. At parameter $1$, stable influence equals ordinary influence (\texttt{stableInfluence_one_eq_influence}), so this inequality is exactly the desired one.

**Key facts.** `FABL.RegularUniqueGame.stableInfluence_uniformExpectation_le`, `FABL.stableInfluence_one_eq_influence`.
