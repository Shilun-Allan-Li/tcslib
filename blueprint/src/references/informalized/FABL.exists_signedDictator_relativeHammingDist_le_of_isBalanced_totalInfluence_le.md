<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RobustEdgeIsoperimetry.lean :: FABL.exists_signedDictator_relativeHammingDist_le_of_isBalanced_totalInfluence_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closeness to a Signed Dictator

**Claim.** If a Boolean function on the sign cube is balanced and has total influence at most $1+\delta$, then some signed dictator is within relative Hamming distance $\delta$ of it.

**Proof.** Balance forces the dimension to be positive, so choose a coordinate $i$ whose singleton Fourier coefficient has maximal absolute value, and write $c=\widehat f(\{i\})$. The balanced influence inequality gives $2-I[f]\le W_1(f)$, hence $1-\delta\le W_1(f)$. On the other hand, the level-one weight is the sum of the squared singleton coefficients. Each coefficient's absolute value is at most $|c|$, and (by the singleton coefficient influence bound) at most its coordinate influence. Term by term, this yields $W_1(f)\le |c|I[f]\le |c|(1+\delta)$. Since $W_1(f)\le1$, we also have $|c|\le1$, so $|c|(1+\delta)\le |c|+\delta$. Combining these inequalities gives $|c|\ge1-2\delta$. The dictator at coordinate $i$ is the singleton character, so its correlation with $f$ is $c$. If $c\ge0$, use that dictator; if $c<0$, use its negation, whose correlation with $f$ is $-c=|c|$. In either case the correlation is at least $1-2\delta$. Correlation equals one minus twice the relative Hamming distance, so the chosen signed dictator is at distance at most $\delta$.

**Key facts.** `FABL.positive_dimension_of_isBalanced`, `FABL.two_sub_totalInfluence_le_fourierWeightAtLevel_one_of_isBalanced`, `FABL.fourierWeightAtLevel_one_eq_sum_singleton`, `FABL.abs_fourierCoeff_singleton_le_influence`, `FABL.fourierWeightAtLevel_one_mem_Icc`, `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.fourierCoeff_eq_uniformInner`, `FABL.uniformInner_eq_one_sub_two_mul_relativeHammingDist`, `FABL.BooleanFunction.toReal_neg`.
