<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_le_mutualInfo_of_condDependence_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditioning monotonicity for mutual information

**Claim.** If $I[X:W\mid Y;\mu]\le I[X:W;\mu]$, then $I[X:Y\mid W;\mu]\le I[X:Y;\mu]$.

**Proof.** Regard the ordered pairs $(Y,W)$ and $(W,Y)$ as two encodings of the same joint information. Swapping the coordinates is an injective map, and applying an injective recoding to the second variable preserves mutual information (\texttt{mutualInfo\_comp\_right\_of\_injective}); hence $I[X:(Y,W);\mu]=I[X:(W,Y);\mu]$. Apply the chain rule for mutual information in each coordinate order (\texttt{mutualInfo\_prod\_right\_eq\_add}): the first expression is $I[X:Y;\mu]+I[X:W\mid Y;\mu]$, while the second is $I[X:W;\mu]+I[X:Y\mid W;\mu]$. Substituting the assumed inequality into these equal expressions and subtracting the common terms yields $I[X:Y\mid W;\mu]\le I[X:Y;\mu]$.

**Key facts.** `ProbabilityTheory.mutualInfo_comp_right_of_injective`, `ProbabilityTheory.mutualInfo_prod_right_eq_add`.
