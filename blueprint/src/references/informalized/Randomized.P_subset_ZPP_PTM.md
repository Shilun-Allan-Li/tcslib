<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.P_subset_ZPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Lies in ZPP

**Claim.** Every language decidable by a finite deterministic Turing machine in polynomial time belongs to ZPP, with zero error and polynomial expected running time in the stated tail-sum formulation.

**Proof.** Write $P$ and `ZPP_PTM` as unions over polynomial exponents. For each exponent, the deterministic time class with bound $n^k+1$ is contained in the corresponding zero-error randomized time class, by `DTIME_subset_ZTIME`. Applying this inclusion to every member of the union gives the claimed containment.

**Key facts.** `Randomized.DTIME_subset_ZTIME`.
