<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.f₂CubeOfFinset_insert_zero_tailFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator with an Initial Coordinate

**Claim.** For every finite set $T\subseteq\mathrm{Fin}(n)$, the indicator of the set formed by adjoining $0$ to the one-place shifts of elements of $T$ has initial coordinate $1$ and tail equal to the indicator of $T$.

**Proof.** Compare the two vectors coordinate by coordinate. At the initial coordinate, the set contains $0$, so its indicator is $1$, as is the initial coordinate of the stated vector. Every other coordinate has the form $j+1$ for a unique $j\in\mathrm{Fin}(n)$. Such a coordinate belongs to the shifted set exactly when $j$ belongs to $T$, so its indicator equals the $j$th coordinate of the indicator of $T$. These are precisely the coordinates of the stated tail.
