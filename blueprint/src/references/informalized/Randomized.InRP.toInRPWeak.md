<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InRP.toInRPWeak -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak randomized recognition from RP

**Claim.** If $L$ has an RP verifier with acceptance probability at least $2/3$ on members and certain rejection on nonmembers, then for any natural number $c$ it has a verifier with member acceptance probability at least $\min\{2/3,(|x|+1)^{-c}\}$ and the same certain rejection guarantee.

**Proof.** Unpack the RP verifier and retain its machine and polynomial random-bit bound. For each member, the acceptance probability is at least $2/3$. The minimum of $2/3$ and $(|x|+1)^{-c}$ is at most $2/3$, so the existing guarantee implies the weaker stated lower bound. For nonmembers, keep the original pointwise rejection guarantee unchanged.
