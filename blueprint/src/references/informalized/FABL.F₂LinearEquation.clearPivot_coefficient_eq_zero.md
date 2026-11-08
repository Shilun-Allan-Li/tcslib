<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.F₂LinearEquation.clearPivot_coefficient_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pivot coefficient after clearing

**Claim.** If the pivot equation has coefficient $1$ at the pivot variable, clearing that pivot from the row equation leaves coefficient $0$ there.

**Proof.** There are two cases. If the row already has coefficient $0$ at the pivot, the clearing operation leaves the row unchanged, so the result follows immediately. Otherwise, since the field has exactly two elements, the row coefficient is $1$. Clearing then adds the pivot equation, whose pivot coefficient is also $1$. Their sum is $1+1=0$ in $\mathbb F_2$, as required.
