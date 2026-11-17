<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.firstCoordinateSlice_one_degree_le_pred_of_zero_slice_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Drop When the Zero Slice Vanishes

**Claim.** If the zero slice of a Boolean function on $\mathbb F_2^{n+1}$ vanishes and the function has algebraic degree at most $k$, then its one slice has algebraic degree at most $k-1$.

**Proof.** By the degree characterization, it suffices to bound the size of any set $S$ whose ANF coefficient in the one slice is nonzero (\texttt{algebraicDegree\_le\_iff}). The one-slice coefficient is the sum of the coefficients of $f$ at the tail frequency and at the frequency with the first coordinate adjoined (\texttt{anfCoeff\_firstCoordinateSlice\_one}). The zero-slice coefficient equals the coefficient at the tail frequency (\texttt{anfCoeff\_firstCoordinateSlice\_zero}); because the zero slice is the zero function, that coefficient vanishes. Consequently the one-slice coefficient equals the coefficient at the frequency with the first coordinate adjoined, and this coefficient is nonzero. The degree bound on $f$ bounds the size of that enlarged frequency by $k$. Since the first coordinate is absent from the tail frequency and tail frequencies preserve cardinality, the enlarged frequency has size $|S|+1$ (\texttt{zero\_notMem\_tailFrequency}, \texttt{card\_tailFrequency}). Thus $|S|+1\le k$, so $|S|\le k-1$, as required.

**Key facts.** `FABL.algebraicDegree_le_iff`, `FABL.anfCoeff_firstCoordinateSlice_one`, `FABL.anfCoeff_firstCoordinateSlice_zero`, `FABL.card_tailFrequency`, `FABL.zero_notMem_tailFrequency`.

**Caveat.** The supplied informal statement describes a support-size lemma by induction, but the formal statement and proof establish this degree-drop result for a Boolean function whose zero slice vanishes.
