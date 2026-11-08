<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.restricted_length_identity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length under coordinate restriction

**Claim.** The Euclidean length built from the restricted function's Gaussian profile, its derivatives in the first n coordinates, and the last-coordinate half-difference equals the corresponding length for the original function at the appended point.

**Proof.** The expression inside the outer square root on the left is the sum of the squares of the restricted length and the last-coordinate half-difference. Since the restricted length is a square root of a nonnegative quantity, squaring that inner square root recovers the profile square plus the sum of the first n derivative squares. The derivative-sum decomposition (`sum_sq_derivative_snoc`) identifies the sum of all n+1 derivative squares of the original function with precisely those first n squares plus the last-coordinate half-difference square. After unfolding restriction, the two radicands agree, so their square roots agree.

**Key facts.** `BooleanAnalysis.GaussianSpace.sum_sq_derivative_snoc`.
