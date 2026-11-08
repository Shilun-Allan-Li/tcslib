<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNOptimality.lean :: FABL.firstCoordinateSlice_fknOptimalityFunction_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Slice of the Optimality Function

**Claim.** For every $q\in\mathbb N$, fixing the first coordinate of the real-valued sign embedding of the optimality Boolean function to $1$ gives the constant function with value $1$ on the tail coordinates.

**Proof.** Evaluate both functions at an arbitrary tail vector $x$. The real-valued optimality function at the vector with first coordinate $1$ equals $1$, by the corresponding slice evaluation identity (\texttt{fknOptimalityFunction\_toReal\_cons\_one}). Hence the two functions agree at every $x$.

**Key facts.** `FABL.fknOptimalityFunction_toReal_cons_one`.
