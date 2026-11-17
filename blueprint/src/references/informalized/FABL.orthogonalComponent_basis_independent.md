<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.orthogonalComponent_basis_independent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Basis independence of orthogonal components

**Claim.** For any two finite Fourier bases, the component of $f$ indexed by a coordinate set $S$ is the same for both bases.

**Proof.** Apply the Möbius inversion formula for orthogonal components to each basis. It expresses the component indexed by $S$ as the same alternating sum over subsets $J\subseteq S$ of the coordinate projections of $f$: $\sum_{J\subseteq S}(-1)^{|S|-|J|}\,\operatorname{projectOnCoordinates}_{J}(f)$. This expression depends on the product measure and the coordinate set, but not on the choice of Fourier basis. The two components are therefore equal (\texttt{FABL.FiniteFourierBasis.orthogonalComponent\_eq\_mobius}).

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_eq_mobius`.
