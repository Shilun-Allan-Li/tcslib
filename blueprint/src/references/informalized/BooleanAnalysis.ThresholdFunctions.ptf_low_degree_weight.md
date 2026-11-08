<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Fourier.lean :: BooleanAnalysis.ThresholdFunctions.ptf_low_degree_weight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-Degree Fourier Weight of Threshold Functions

**Claim.** Every degree-at-most-$k$ polynomial threshold function taking values in $\{-1,1\}$ has Fourier weight on levels up to $k$ at least $e^{-2k}$.

**Proof.** Use the general lower bound that compares low-degree Fourier weight with an $L^1$-to-$L^2$ inequality for every degree-at-most-$k$ polynomial (\texttt{le_fourierWeightUpTo_of_l1_l2}). It suffices to take its constant $c=e^{-2k}$, which is at most $1$. The required inequality for a representing polynomial is exactly the squared low-degree $L^1$–$L^2$ bound: its squared $L^1$ norm dominates $e^{-2k}$ times the sum of squares of its coefficients (\texttt{low_degree_l1_l2_sq}). Applying the general comparison yields the stated lower bound for the Fourier weight.

**Key facts.** `BooleanAnalysis.ThresholdFunctions.le_fourierWeightUpTo_of_l1_l2`, `BooleanAnalysis.ThresholdFunctions.low_degree_l1_l2_sq`.
