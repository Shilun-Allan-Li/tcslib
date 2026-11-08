<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/General.lean :: BooleanAnalysis.Hypercontractivity.rpow_norm_le_of_sq_moments -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Taking square roots of moment bounds

**Claim.** If $A,B\ge 0$ and $A^{2/q}\le B^{2/p}$, then $A^{1/q}\le B^{1/p}$.

**Proof.** Both $A^{1/q}$ and $B^{1/p}$ are nonnegative, since real powers of nonnegative bases are nonnegative. The hypothesis and the laws of real powers identify their squares with $A^{2/q}$ and $B^{2/p}$, respectively. Thus $(A^{1/q})^2\le(B^{1/p})^2$; for nonnegative quantities, comparison of squares implies comparison of the quantities themselves.
