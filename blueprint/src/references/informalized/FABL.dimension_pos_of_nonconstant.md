<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.dimension_pos_of_nonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonconstant Functions Require Positive Dimension

**Claim.** If a sign-valued function on the $n$-dimensional sign cube is nonconstant, then $n>0$.

**Proof.** Suppose instead that $n$ is not positive. Since $n$ is a natural number, this forces $n=0$. Nonconstancy supplies two cube points $x,y$ on which the function differs. But in dimension zero there are no coordinates: any two functions on the empty coordinate type are equal, by function extensionality. Thus $x=y$, contradicting that their function values differ. Therefore $n>0$.
