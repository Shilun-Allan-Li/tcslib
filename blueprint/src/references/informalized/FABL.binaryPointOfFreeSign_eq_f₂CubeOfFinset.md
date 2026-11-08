<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/SpectralDegree.lean :: FABL.binaryPointOfFreeSign_eq_f₂CubeOfFinset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Point from Free Signs

**Claim.** For every $n$, every set $J$ of coordinates in $\{0,\ldots,n-1\}$, and every assignment $y$ of signs to the coordinates in $J$, combine $y$ with the constant $+1$ assignment on the remaining coordinates and convert the resulting sign vector to a binary vector. This binary vector is the indicator vector, over $\mathbb F_2$, of the set of coordinates in $J$ where $y$ equals $-1$.

**Proof.** Compare the two vectors at an arbitrary coordinate $i$, splitting into whether $i$ belongs to $J$. If $i\in J$, the combined sign at $i$ is $y(i)$ ($\texttt{combineSignCube_apply_free}$). The binary coordinate obtained from this sign is $1$ exactly when its binary encoding is nonzero. The lifted set of nonzero coordinates records precisely those free coordinates: membership in the lifted set is equivalent to the binary encoding of $y(i)$ being nonzero. Since a binary coordinate is either $0$ or $1$, this is exactly the indicator value. If $i\notin J$, the combined sign is the fixed value $+1$ ($\texttt{combineSignCube_apply_fixed}$), whose binary encoding is $0$; the coordinate is also absent from the lifted set, so the indicator is $0$. The coordinatewise equalities establish equality of the vectors; the indicator-coordinate description is $\texttt{f₂CubeOfFinset_apply}$.

**Key facts.** `FABL.combineSignCube_apply_free`, `FABL.f₂CubeOfFinset_apply`, `FABL.combineSignCube_apply_fixed`.
