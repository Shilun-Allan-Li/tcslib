<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.card_pairingPerm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairings as Permutations

**Claim.** For every natural number $m$, the number of permutations of $2m$ elements whose cycle decomposition consists of exactly $m$ cycles of length two is $(2m-1)!!$.

**Proof.** The permutations in question are precisely those whose cycle type is the multiset containing $m$ copies of $2$. The cycle-type counting formula says that the number of permutations with this cycle type is $(2m)!/(2^m m!)$: the factors of $2$ account for rotations within each two-cycle, and the factor $m!$ accounts for reordering the cycles. For $m=0$, this gives one permutation, as claimed. For positive $m$, use the factorial identity $(2m)!=(2^m m!)(2m-1)!!$. Comparing the two expressions and cancelling the positive factor $2^m m!$ gives the result.
