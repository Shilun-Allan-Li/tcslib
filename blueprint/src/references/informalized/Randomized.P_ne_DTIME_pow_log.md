<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.P_ne_DTIME_pow_log -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial and Logarithmic-Power Time

**Claim.** The class of languages decidable by finite deterministic Turing machines in polynomial time is not equal to the class decidable in time $n^{\log_2 n}$ up to a constant multiplicative factor.

**Proof.** The strict-inclusion theorem `P_ssubset_DTIME_pow_log` states that the polynomial-time class is a proper subset of the indicated logarithmic-power time class. Proper inclusion entails that the two classes are unequal, which is the claimed conclusion.

**Key facts.** `Randomized.P_ssubset_DTIME_pow_log`.
