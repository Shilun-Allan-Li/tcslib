<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.firstCoordinateSlice_one_degree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for the One Slice

**Claim.** If a Boolean function on $\mathbb F_2^{n+1}$ has algebraic degree at most $k$, then its slice obtained by fixing the first coordinate to $1$ also has algebraic degree at most $k$.

**Proof.** Use the characterization of degree at most $k$ by the condition that every nonzero ANF coefficient is indexed by a set of size at most $k$ (\texttt{algebraicDegree\_le\_iff}). Fix a set $S$ whose coefficient in the one slice is nonzero. That coefficient is the sum over $\mathbb F_2$ of the coefficient of $f$ at the tail frequency and the coefficient at the frequency with the first coordinate adjoined (\texttt{anfCoeff\_firstCoordinateSlice\_one}). A nonzero sum has at least one nonzero summand. The degree hypothesis therefore bounds the size of one of these two frequencies by $k$. The tail frequency has size $|S|$, and the frequency with the first coordinate adjoined has size $|S|+1$ (\texttt{card\_tailFrequency}; the first coordinate is not already in the tail frequency by \texttt{zero\_notMem\_tailFrequency}). In either case $|S|\le k$, which proves the degree bound for the slice.

**Key facts.** `FABL.algebraicDegree_le_iff`, `FABL.anfCoeff_firstCoordinateSlice_one`, `FABL.card_tailFrequency`, `FABL.zero_notMem_tailFrequency`.

**Caveat.** The supplied informal statement describes a support-size lemma about a nonzero real-valued function, but the formal statement and proof establish the stated algebraic-degree bound for a Boolean one-slice.
