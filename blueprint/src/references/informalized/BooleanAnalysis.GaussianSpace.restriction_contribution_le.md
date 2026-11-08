<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov.lean :: BooleanAnalysis.GaussianSpace.restriction_contribution_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted contribution bound

**Claim.** Under the stated profile bound for the restricted function, the square root combining its profile at the mean with the mean last-coordinate half-difference is at most the expected full length of the original function on the chosen slice.

**Proof.** First apply `sqrt_profile_sq_le` to the assumed bound on the profile at the mean. This replaces that profile by the Bobkov functional while retaining the squared mean half-difference. The resulting expression is the Euclidean norm of the expectations of two functions: the pointwise length of the restricted function and its last-coordinate half-difference. The inequality `sqrt_expect_sq_add_sq_le_expect_sqrt` bounds this norm by the expectation of their pointwise Euclidean norm. At each point, `restricted_length_identity` identifies that pointwise norm with the full profile-and-derivative length of the original function at the appended point. Substituting this identity yields the claimed bound.

**Key facts.** `BooleanAnalysis.GaussianSpace.sqrt_profile_sq_le`, `BooleanAnalysis.GaussianSpace.sqrt_expect_sq_add_sq_le_expect_sqrt`, `BooleanAnalysis.GaussianSpace.restricted_length_identity`.
