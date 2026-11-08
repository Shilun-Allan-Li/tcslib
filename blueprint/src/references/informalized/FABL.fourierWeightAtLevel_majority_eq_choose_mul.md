<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityWeightMonotonicity.lean :: FABL.fourierWeightAtLevel_majority_eq_choose_mul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority weight from symmetry

**Claim.** For any $n,k$, and any set $S$ of size $k$, the level-$k$ Fourier weight of majority equals $\binom nk$ times the squared Fourier coefficient at $S$.

**Proof.** Majority is invariant under permutations of the coordinates, so its real-valued version is symmetric. For a symmetric function, Fourier coefficients on sets of equal cardinality agree (`fourierCoeff_eq_of_card_eq_of_isSymmetric`). Consequently, every summand in the level-$k$ weight is the same squared coefficient as the one at $S$. There are exactly $\binom nk$ subsets of size $k$, so summing these equal terms gives the formula.

**Key facts.** `FABL.majority_symmetric`, `FABL.fourierCoeff_eq_of_card_eq_of_isSymmetric`.
