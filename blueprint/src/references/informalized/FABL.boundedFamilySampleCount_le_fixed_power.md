<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.boundedFamilySampleCount_le_fixed_power -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Sample Bound in Dimension

**Claim.** Under the stated sub-square-root regime assumptions, the bounded-family sample count with the learning-consequences family bound is at most the stated fixed polynomial in $n+1$.

**Proof.** Set $M$ equal to the learning-consequences family bound. The family-bound estimate gives $M\le A(n+1)^E$, where $A=2^{2e}$ and $E=e$ are the specified family constant and exponent. The regime also yields $(1/\varepsilon)^2\le (Q+1)^2$. The general bounded-family sample estimate therefore gives a bound by $640M^3/\varepsilon^2$, and the cubic sample-expression estimate, applied with these bounds on $M$ and $1/\varepsilon$, bounds this by $640A^3Q^2(n+1)^{3E}$ in its stated notation. Rewriting that coefficient and exponent using the definitions of the second-stage sample constant and exponent gives the claimed natural-number bound.

**Key facts.** `FABL.boundedFamilySampleCount_cast_le`, `FABL.learningConsequencesFamilyBound_le_fixed_power`, `FABL.one_div_accuracy_pow_le`, `FABL.cubicSampleExpression_le_fixed_power`.
