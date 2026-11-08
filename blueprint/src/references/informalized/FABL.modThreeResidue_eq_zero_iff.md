<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.modThreeResidue_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Residue and divisibility

**Claim.** The sum of the coordinates reduced modulo $3$ is zero exactly when their integer sum is divisible by $3$.

**Proof.** First identify the residue sum with the image in $\mathbb{Z}/3\mathbb{Z}$ of the integer coordinate sum: reduction modulo $3$ preserves finite sums, so $\mathrm{modThreeResidue}(x)=(\mathrm{signCoordinateIntegerSum}(x):\mathbb{Z}/3\mathbb{Z})$. An integer has zero image modulo $3$ exactly when it is divisible by $3$. Applying this criterion to the coordinate sum gives the stated equivalence.
