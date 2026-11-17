<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/AffineKhintchine.lean :: BooleanAnalysis.ThresholdFunctions.affine_sum_antipode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Antipodal Sum of an Affine Walsh Polynomial

**Claim.** If the coefficients of a real multilinear polynomial vanish on sets of size greater than one, then its Walsh polynomial at a Boolean vector and at the coordinatewise complement sum to twice its constant coefficient.

**Proof.** By the degree-one evaluation formula (`eval_of_degree_le_one`), each value is the constant coefficient plus a sum over coordinates of the singleton coefficient times the sign of that coordinate. Under complementation, each sign changes to its negative (`boolToSign_not`). Thus the two coordinate sums cancel term by term, leaving two copies of the constant coefficient.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_of_degree_le_one`, `BooleanAnalysis.boolToSign_not`.
