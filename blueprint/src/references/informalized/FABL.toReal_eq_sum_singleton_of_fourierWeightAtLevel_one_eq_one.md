<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/InfluencesAndDerivatives/DegreeOneRigidity.lean :: FABL.toReal_eq_sum_singleton_of_fourierWeightAtLevel_one_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Level-One Fourier Expansion

**Claim.** If the total Fourier weight of a Boolean function at level one is $1$, then at every input its real-valued form equals the sum of its singleton Fourier coefficients times the corresponding coordinate signs.

**Proof.** By the Fourier expansion theorem (`FABL.fourier_expansion`), the value at $x$ is the sum over all subsets $S$ of the Fourier coefficient at $S$ times the monomial indexed by $S$. Restrict this sum to subsets of cardinality one: every other term vanishes by the consequence of the level-one weight hypothesis that coefficients outside level one are zero (`FABL.fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one`). Finally, subsets of cardinality one are exactly the singletons $\\{i\\}$, and the monomial of such a singleton is the sign at coordinate $i$. Reindexing the remaining finite sum by $i$ gives the stated formula.

**Key facts.** `FABL.fourier_expansion`, `FABL.fourierCoeff_eq_zero_of_fourierWeightAtLevel_one_eq_one`.
