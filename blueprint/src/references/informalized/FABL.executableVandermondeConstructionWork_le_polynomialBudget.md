<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableVandermonde.lean :: FABL.executableVandermondeConstructionWork_le_polynomialBudget -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Construction Work Bound

**Claim.** For an input with independence order $k$ and dimension $n$, the executable Vandermonde construction work is at most $2^{17}(	ext{scale}+1)^8$, where $	ext{scale}=n^k$.

**Proof.** Put $N=n+1$, let $d$ be the field degree, and put $p=k-1$. The field-degree bound gives $d+1\le 4N$, while $p\le N$. Also, the field-size estimate $2^d\le 2n$ implies $2^{d+1}\le 4N$. By the preprocessing estimate (`binaryFieldPreprocessingWork_le`), the field preprocessing work is at most $2^{8(d+1)}=(2^{d+1})^8\le 2^{16}N^8$.

The binary arithmetic estimate (`binaryArithmeticWork_le`) bounds one modular multiplication by $8(d+1)^2\le128N^2$. The power-row estimate (`executableVandermondePowerRowsWork_le`) then gives at most $138N^4$ work for the $p$ rows: indeed, its bracket is bounded by $138N^3$ using $p\le N$, the multiplication bound, and $d\le4N$. Adding one unit gives at most $139N^4$; multiplying by $n\le N$ bounds the matrix-row construction work by $139N^5$. Combining both stages, and using $N^5\le N^8$, bounds total work by $2^{17}N^8$.

Finally, since $k\ge1$, $n\le n^k=\text{scale}$, so $N\le\text{scale}+1$. Raising this inequality to the eighth power yields the claimed budget bound.

**Key facts.** `FABL.ExecutableVandermondeInput.fieldDegree_succ_le`, `FABL.ExecutableVandermondeInput.fieldSize_le_two_n`, `FABL.binaryFieldPreprocessingWork_le`, `FABL.binaryArithmeticWork_le`, `FABL.executableVandermondePowerRowsWork_le`, `FABL.executableVandermondeConstructionWork_eq`.
