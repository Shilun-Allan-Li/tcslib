<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Yap.lean :: Complexity.Yap.Data.mem_checkLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Check-Language Membership

**Claim.** A bit string $q$ belongs to the check language exactly when the check holds on the first and second decoded components of the first decoded component of $q$, and on the second decoded component of $q$.

**Proof.** By definition, the check language contains precisely the strings satisfying this check condition. Unfolding the definition gives the stated equivalence.
