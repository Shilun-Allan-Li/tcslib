<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/AlmostKWiseAlgorithm.lean :: FABL.almostKWiseVandermondeWork_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vandermonde Construction Work Bound

**Claim.** The work of the almost-wise Vandermonde construction is at most $2^{17}(	ext{scale}+1)^8$.

**Proof.** Set $R=	ext{scale}+1$, let $d$ be the Vandermonde field degree, and put $p=k-1$. The scale bound `AlmostKWiseInput.n_le_scale` gives $nR$ and, using $ku2264n$, also $pR$. The field-degree bound `ExecutableVandermondeInput.fieldDegree_succ_le`, together with $nR$, yields $d+14R$. The field-size bound `ExecutableVandermondeInput.fieldSize_le_two_n` then gives $2^{d+1}4R$.

The preprocessing estimate (`binaryFieldPreprocessingWork_le`) bounds field setup by $2^{8(d+1)}=(2^{d+1})^8$, hence by $2^{16}R^8$. The arithmetic estimate (`binaryArithmeticWork_le`) bounds modular multiplication by $8(d+1)^2$, hence by $128R^2$. Using $pR$, the power-row estimate (`executableVandermondePowerRowsWork_le`) bounds the row work by $138R^4$, and therefore the row work plus one by $139R^4$. Since $nR$, the matrix-construction contribution is at most $139R^5$.

The work identity (`executableVandermondeConstructionWork_eq`) expresses total work as preprocessing plus this matrix contribution. Since $R1$, we have $R^5R^8$. Thus the total is at most $2^{16}R^8+139R^82^{17}R^8$, as required.

**Key facts.** `FABL.AlmostKWiseInput.n_le_scale`, `FABL.ExecutableVandermondeInput.fieldDegree_succ_le`, `FABL.ExecutableVandermondeInput.fieldSize_le_two_n`, `FABL.binaryFieldPreprocessingWork_le`, `FABL.binaryArithmeticWork_le`, `FABL.executableVandermondePowerRowsWork_le`, `FABL.executableVandermondeConstructionWork_eq`.
