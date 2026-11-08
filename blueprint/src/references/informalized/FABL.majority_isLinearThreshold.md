<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/Definitions.lean :: FABL.majority_isLinearThreshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority as a Linear Threshold

**Claim.** For every natural number $n$, majority on $n$ signs is a linear threshold function: one may choose a real bias and coordinate weights so that majority is the threshold sign of their weighted input sum.

**Proof.** Choose bias $0$ and assign weight $1$ to every coordinate. Then the weighted sum on any sign vector is exactly its coordinate sum. By the definition of majority, its value is the threshold sign of this sum, which is the required representation.
