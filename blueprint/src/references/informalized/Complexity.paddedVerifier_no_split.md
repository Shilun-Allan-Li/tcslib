<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.paddedVerifier_no_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection When No Split Exists

**Claim.** If no $n\le |y|$ satisfies $n+(C+1)(n+1)^c=|y|$, then $y$ does not belong to the padded verifier for $C,c,V$.

**Proof.** The padded verifier's membership conditions include a split point $n$ for which the split function at length $|y|$ returns `some n`. The assumed failed split says it returns `none`. These two values cannot be equal, so the required membership witness is impossible.
