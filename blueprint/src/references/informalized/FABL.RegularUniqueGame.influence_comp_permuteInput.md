<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.influence_comp_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Influence Under Input Permutation

**Claim.** For any coordinate, the influence of $x\mapsto f(x\circ\pi)$ at that coordinate equals the influence of $f$ at its inverse image under the permutation.

**Proof.** Stable influence is invariant under permuting the input coordinates, with the measured coordinate carried back by the inverse permutation (\texttt{stableInfluence_comp_permuteInput}). Apply this identity at parameter $1$. At that parameter, stable influence equals ordinary influence (\texttt{stableInfluence_one_eq_influence}); replacing both stable influences by ordinary influence gives the asserted equality.

**Key facts.** `FABL.RegularUniqueGame.stableInfluence_comp_permuteInput`, `FABL.stableInfluence_one_eq_influence`.
