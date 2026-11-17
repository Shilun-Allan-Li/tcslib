<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/ExtremalBounds.lean :: FABL.f₂CubeOfFinset_tailFrequency -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator after Shifting Coordinates

**Claim.** For every finite set $T\subseteq\mathrm{Fin}(n)$, the indicator of the set obtained by shifting each element of $T$ one place into $\mathrm{Fin}(n+1)$ has initial coordinate $0$ and tail equal to the indicator of $T$.

**Proof.** Compare coordinates. The initial coordinate $0$ is not in the shifted set, so its indicator is $0$. Every other coordinate is uniquely of the form $j+1$ with $j\in\mathrm{Fin}(n)$; it belongs to the shifted set exactly when $j\in T$. Thus the remaining coordinates agree with the indicator vector of $T$, as claimed.
