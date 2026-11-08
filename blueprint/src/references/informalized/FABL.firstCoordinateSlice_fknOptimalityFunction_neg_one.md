<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.firstCoordinateSlice_fknOptimalityFunction_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative Slice of the Optimality Function

**Claim.** For every $q\in\mathbb N$, fixing the first coordinate of the real-valued sign embedding of the optimality Boolean function to $-1$ gives the function $x\mapsto 2A_q(x)-1$, where $A_q$ is the small-set indicator on the tail coordinates.

**Proof.** To prove equality of the two functions, evaluate them at an arbitrary tail vector $x$. The value of the real-valued optimality function on the vector with first coordinate $-1$ is $2A_q(x)-1$, by the slice evaluation identity for this function (\texttt{fknOptimalityFunction\_toReal\_cons\_neg\_one}). Since the values agree for every $x$, the functions are equal.

**Key facts.** `FABL.fknOptimalityFunction_toReal_cons_neg_one`.
