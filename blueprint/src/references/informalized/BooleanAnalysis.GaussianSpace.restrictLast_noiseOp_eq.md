<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/Noise.lean :: BooleanAnalysis.GaussianSpace.restrictLast_noiseOp_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise and last-coordinate restriction

**Claim.** For either last-coordinate bit, restricting the noise operator applied to a function gives the noise of its average restriction plus the signed, noise-smoothed half-difference.

**Proof.** Fix a point of the smaller cube and evaluate both sides there. The definition of restriction identifies the left side with the noise operator evaluated at the point obtained by appending the chosen bit. The last-coordinate decomposition formula for the noise operator (`noiseOp_snoc`) says this value is the noise of the average restriction plus the bit's sign times the parameter and the noise of the half-difference. Rewriting the scalar factors gives exactly the asserted equality of functions.

**Key facts.** `BooleanAnalysis.Hypercontractivity.noiseOp_snoc`.
