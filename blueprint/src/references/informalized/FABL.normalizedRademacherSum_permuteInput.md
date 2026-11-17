<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.normalizedRademacherSum_permuteInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Permutation Invariance

**Claim.** For every natural number $n$, permutation of the coordinates leaves the normalized sign sum unchanged.

**Proof.** Expanding the sum after permuting the input gives a sum over indices $i$ of the common coefficient times the value of the original vector at $\pi(i)$. Because a permutation is a bijection of the coordinate set, reindexing this finite sum by $\pi$ gives exactly the original sum. This is the invariance of a finite sum under composition with an equivalence (`Equiv.sum_comp`).
