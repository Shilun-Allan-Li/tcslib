<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_cond_specialZeroZero_measureReal_le_two_mul_disjointSpecialYFalseMeasure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A factor-two conditioning bound

**Claim.** For every set $S$ of hard samples, the measure conditioned on both special bits being false assigns $S$ at most twice the measure conditioned on disjointness and then on Bob's special bit being false.

**Proof.** Write $\mu$ for the measure conditioned on disjointness, and let $Y_0$ be the event that Bob's special bit is false. The event that both special bits are false is contained in $Y_0$. Because it is also contained in the disjointness event (the fact that the zero-zero special-bit event implies disjointness, `specialZeroZero_subset_disjointEvent`), conditioning the original measure on it gives the same conditional measure as conditioning $\mu$ on it (`volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent`). For any event $B$, conditioning a probability measure on $B$ gives mass $\mu(B)^{-1}\mu(B\cap S)$. Thus the two sides in the claimed comparison are respectively $3\mu(\text{zero-zero}\cap S)$ and $\tfrac32\mu(Y_0\cap S)$: the denominators are $1/3$ and $2/3$, since the zero-zero event has mass $1/3$ (`disjointCondMeasure_measureReal_specialZeroZero`) and $Y_0$ has mass $2/3$ (`disjointCondMeasure_measureReal_specialY_false`). By event inclusion, $\mu(\text{zero-zero}\cap S)\leq\mu(Y_0\cap S)$. Multiplying this inequality by $3$ gives the desired bound.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialZeroZero_subset_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_cond_eq_disjointCondMeasure_cond_of_subset_disjointEvent`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialZeroZero`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialY_false`.
