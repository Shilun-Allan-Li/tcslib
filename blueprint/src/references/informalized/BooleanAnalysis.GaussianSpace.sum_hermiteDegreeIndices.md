<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Hermite/Truncation.lean :: BooleanAnalysis.GaussianSpace.sum_hermiteDegreeIndices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over Bounded Hermite Indices

**Claim.** The sum over Hermite indices whose total degree is at most $k$ equals the sum over all coordinate choices in $\{0,\ldots,k\}$, with terms of total degree exceeding $k$ replaced by zero.

**Proof.** Every retained index $\alpha$ is represented by a unique function $a$ with values in $\{0,\ldots,k\}$: the defining filtered set keeps exactly the images whose coordinate sum is at most $k$. Conversely, if two such bounded-coordinate functions have the same image as natural-number-valued functions, their values agree at every coordinate, so the functions themselves are equal. Thus the image-sum formula identifies the sum over the image with the sum over the bounded choices, and filtering the image restricts precisely to choices with total degree at most $k$. Writing the restricted sum as a sum over all bounded choices with zero contribution when the degree exceeds $k$ gives the displayed identity.
