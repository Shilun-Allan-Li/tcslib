<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Supremum of mean-zero set integrals

**Claim.** If g is measurable and integrable with mean zero, the supremum of the absolute values of its integrals over measurable sets equals its integral over the region where g is nonnegative.

**Proof.** Let A = {x : g(x) ≥ 0} and let p be the integral of g over A. Since g is nonnegative on A, p ≥ 0. For any measurable S, the integral over S is at most p, by bounding g on S by its nonnegative part. The same bound applies to the integral over the complement of S. Because the total integral is zero, the integral over that complement is the negative of the integral over S. These two bounds show that the absolute value of the integral over S is at most p, so p is an upper bound for the supremum. Finally, A itself is measurable and its integral is p; since p ≥ 0, its absolute integral is p as well. Thus the supremum is at least p, proving equality.
