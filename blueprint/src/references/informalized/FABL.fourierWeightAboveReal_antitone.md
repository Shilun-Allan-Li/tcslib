<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/LowDegree.lean :: FABL.fourierWeightAboveReal_antitone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Fourier weight tails

**Claim.** If $a\le b$, then the Fourier weight over subsets of size greater than $b$ is at most the Fourier weight over subsets of size greater than $a$.

**Proof.** Every subset whose cardinality is greater than $b$ also has cardinality greater than $a$, since $a\le b$. Thus the first tail sums over a subcollection of the subsets in the second tail. Each summand is a squared Fourier coefficient and hence nonnegative. Summing over the smaller collection therefore gives no more than summing over the larger one.
