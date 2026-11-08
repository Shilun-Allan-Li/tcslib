<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.deterministicSmallBiasWork_le_polynomialBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Construction Work Budget

**Claim.** For accuracy data with positive dimension and numerator, and with twice the numerator at most the denominator, the deterministic small-bias construction work is at most $2^{17}(\text{scale}+1)^8$.

**Proof.** Let $q=\text{scale}$, $Q=q+1$, and $d$ be the field degree. We have $Q\ge1$, $q\le Q$, and the dimension bound gives $n\le Q$. The field-size and field-degree bounds (`SmallBiasInput.fieldSize_le_two_scale` and `SmallBiasInput.fieldDegree_succ_le`) imply $2^d\le2Q$ and $d+1\le4Q$. Since $Q\ge1$, these yield $d\le4Q$, $Q\le Q^3$, and the needed comparisons between powers of $Q$.

The preprocessing estimate (`binaryFieldPreprocessingWork_le`) bounds preprocessing work by $2^{8(d+1)}$. Since $2^{d+1}\le4Q$, this is at most $(4Q)^8=2^{16}Q^8$. For the row computation, the arithmetic estimate (`binaryArithmeticWork_le`) bounds modular multiplication work by $8(d+1)^2\le128Q^2$. Multiplying by the dimension gives $n(\text{multiplication work}+1)\le129Q^3$. Along with $d\le4Q$ and $2d\le8Q$, the row-work estimate (`executableSmallBiasRowWork_le`) bounds the total row work by $n(256Q^3)\le256Q^4$.

The construction formula (`executableSmallBiasConstructionWork_eq`) expresses total work as preprocessing plus $2^{2d}$ times row work plus one. We have $2^{2d}\le4Q^2$ and row work plus one at most $257Q^4$, so this latter term is at most $1028Q^6$. Adding the preprocessing bound gives $2^{16}Q^8+1028Q^6\le2^{17}Q^8$, since $Q^6\le Q^8$ and $2^{16}+1028\le2^{17}$. This is the stated budget.

**Key facts.** `FABL.SmallBiasInput.n_le_scale`, `FABL.SmallBiasInput.fieldSize_le_two_scale`, `FABL.SmallBiasInput.fieldDegree_succ_le`, `FABL.binaryFieldPreprocessingWork_le`, `FABL.binaryArithmeticWork_le`, `FABL.executableSmallBiasRowWork_le`, `FABL.executableSmallBiasConstructionWork_eq`.
