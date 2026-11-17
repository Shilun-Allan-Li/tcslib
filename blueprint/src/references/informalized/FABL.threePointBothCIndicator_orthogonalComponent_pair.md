<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.threePointBothCIndicator_orthogonalComponent_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Full Pair Fourier Component

**Claim.** At the full coordinate set, the orthogonal component of the indicator that both coordinates equal $c$ has value $4/9$ when both coordinates equal $c$, $-2/9$ when exactly one does, and $1/9$ when neither does.

**Proof.** Evaluate both sides at an arbitrary pair $x$. The Möbius formula for an orthogonal component (\texttt{FiniteFourierBasis.orthogonalComponent\_eq\_mobius}) expresses the full-support component as the alternating sum of coordinate projections over all subsets $J\subseteq\{0,1\}$. The four subsets are $\varnothing,\{0\},\{1\},\{0,1\}$. By the projection formula (\texttt{projectOnCoordinates\_threePointBothCIndicator}), the contribution for each $J$ is the product over coordinates of the indicator of $c$ on coordinates in $J$, and $1/3$ on coordinates outside $J$; its sign is $(-1)^{2-|J|}$. Splitting into the four possibilities according to whether $x_0=c$ and whether $x_1=c$, and adding these four terms, gives respectively $4/9$, $-2/9$, and $1/9$. These are exactly the cases in the stated value function.

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_eq_mobius`, `FABL.projectOnCoordinates_threePointBothCIndicator`, `FABL.sum_finset_finTwo`.
