<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.boundedCubeFunction_influence_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Bound for Bounded Functions

**Claim.** If a function on the Boolean cube takes values in $[-1,1]$, then the influence of each coordinate is at most $1$.

**Proof.** Apply the stable-influence bound for bounded functions at noise parameter $\rho=1$, which lies in $[0,1]` (`boundedCubeFunction_stableInfluence_le_one`). At this endpoint, stable influence equals ordinary influence (`stableInfluence_one_eq_influence`). Therefore the ordinary influence is at most $1$.

**Key facts.** `FABL.RegularUniqueGame.boundedCubeFunction_stableInfluence_le_one`, `FABL.stableInfluence_one_eq_influence`.
