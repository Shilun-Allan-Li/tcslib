<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Bobkov/DiscreteApproximation.lean :: BooleanAnalysis.GaussianSpace.normalizedBoolBlocks_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating a normalized Boolean block

**Claim.** Replacing entry $x_{ij}$ by $b$ changes the normalized row-sum vector by $\frac{\sigma(b)-\sigma(x_{ij})}{\sqrt m}e_i$.

**Proof.** In row $i$, the updated sum differs from the original sum only at column $j$. Splitting off that summand shows that the new sum is the old sum plus $\sigma(b)-\sigma(x_{ij})$. Dividing by $\sqrt m$ gives the stated change in row $i$. Every other row is unchanged, because updating the outer function at row $i$ leaves its values at all other rows fixed. Thus the vector difference is exactly the stated scalar multiple of the coordinate vector $e_i$. The argument uses only the update and finite-sum identities, so it also covers $m=0$, when there is no column to update and the assertion is vacuous.
