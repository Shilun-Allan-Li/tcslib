<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.firstCoordinateSlice_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for a Binary Slice

**Claim.** If a Boolean function on $\mathbb F_2^{n+1}$ has algebraic degree at most $k$, then fixing its first coordinate to any $b\in\mathbb F_2$ gives a function of algebraic degree at most $k$.

**Proof.** There are only two elements of $\mathbb F_2$. If $b=0$, the conclusion is the degree bound for the zero slice (\texttt{firstCoordinateSlice\_zero\_degree\_le}). If $b\ne0$, then $b=1$, and the degree bound for the one slice (\texttt{firstCoordinateSlice\_one\_degree\_le}) gives the result.

**Key facts.** `FABL.firstCoordinateSlice_zero_degree_le`, `FABL.firstCoordinateSlice_one_degree_le`.
