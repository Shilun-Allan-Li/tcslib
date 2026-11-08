<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeRowCount_cardBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vandermonde Row-Count Bound

**Claim.** For the given input, $2^{(k-1)d+1}\le 2^k n^{k-1}$, where $d$ is the field degree.

**Proof.** Rewrite the left side as $2(2^d)^{k-1}$. The field-size estimate (`ExecutableVandermondeInput.fieldSize_le_two_n`) gives $2^d\le2n$, so monotonicity of natural-number powers bounds this by $2(2n)^{k-1}$. Expanding the power gives $2\cdot2^{k-1}n^{k-1}=2^k n^{k-1}$, using $k\ge1$ to identify $(k-1)+1$ with $k$.

**Key facts.** `FABL.ExecutableVandermondeInput.fieldSize_le_two_n`.
