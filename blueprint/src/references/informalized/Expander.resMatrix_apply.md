<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.resMatrix_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of a row-restricted matrix

**Claim.** The row-restricted matrix has entry $A_{ij}$ when $i\in B$ and entry zero otherwise.

**Proof.** By definition, the restricted matrix is formed from the function that assigns $A_{ij}$ when the row index belongs to $B$ and zero otherwise. Evaluating its entry at $(i,j)$ gives exactly the claimed formula.
