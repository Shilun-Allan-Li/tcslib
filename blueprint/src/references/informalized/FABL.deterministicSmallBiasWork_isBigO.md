<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.deterministicSmallBiasWork_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Construction Work

**Claim.** For every small-bias input, the deterministic construction work is at most $2^{17}(\text{scale}+1)^8$.

**Proof.** Write $q=\text{scale}$, $Q=q+1$, and $d$ for the field degree. The scale bounds the dimension, and the field-size and field-degree estimates give $2^d\le2Q$ and $d+1\le4Q$. The field-preprocessing bound (`binaryFieldPreprocessingWork_le`) then yields
\[\text{preprocessing work}\le 2^{8(d+1)}=(2^{d+1})^8\le(4Q)^8=2^{16}Q^8.\]
The arithmetic-work estimate (`binaryArithmeticWork_le`) gives the modular multiplication work at degree $d$ at most $8(d+1)^2\le128Q^2$. Consequently the per-row power term, after multiplying by the dimension, is at most $129Q^3$. Using $d\le4Q$, this bounds the bracket in the row-work estimate by $256Q^3$. The row-work estimate (`executableSmallBiasRowWork_le`) and $n\le Q$ therefore give row work at most $256Q^4$, and adding one bounds row work plus one by $257Q^4$. The construction formula (`executableSmallBiasConstructionWork_eq`) says the remaining construction term is $2^{2d}$ times row work plus one. Since $2^{2d}=(2^d)^2\le4Q^2$, this term is at most $1028Q^6$. Combining preprocessing and construction terms gives at most $2^{16}Q^8+1028Q^6$. Because $Q\ge1$, we have $Q^6\le Q^8$, and $2^{16}+1028\le2^{17}$; hence the total is at most $2^{17}Q^8$, as claimed.

**Key facts.** `FABL.SmallBiasInput.n_le_scale`, `FABL.SmallBiasInput.fieldSize_le_two_scale`, `FABL.SmallBiasInput.fieldDegree_succ_le`, `FABL.binaryFieldPreprocessingWork_le`, `FABL.binaryArithmeticWork_le`, `FABL.executableSmallBiasRowWork_le`, `FABL.executableSmallBiasConstructionWork_eq`.
