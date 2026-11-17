<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/LinearThresholdInfluence.lean :: BooleanAnalysis.ThresholdFunctions.IsLinearThreshold.exists_affine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine form of a linear threshold

**Claim.** Every linear threshold function on the Boolean cube can be represented as the threshold sign of a constant plus a weighted sum of the coordinate signs.

**Proof.** Choose a polynomial $p$ of degree at most one whose threshold is $f$. Set the constant term to $p(\varnothing)$ and the weight of coordinate $i$ to $p(\{i\})$. The degree-one evaluation formula says that at each input $x$, $p$ evaluates to this constant plus the sum of those weights times the coordinate signs (\texttt{MultilinearPolynomial.eval_of_degree_le_one}). Taking threshold signs on both sides, and using that $p$ represents $f$, gives the claimed representation.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_of_degree_le_one`.
