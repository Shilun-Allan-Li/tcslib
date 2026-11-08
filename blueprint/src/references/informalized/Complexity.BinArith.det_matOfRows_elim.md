<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetModMath.lean :: Complexity.BinArith.det_matOfRows_elim -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Determinant Under Pivot Elimination

**Claim.** Under the stated prime-modulus, shape, nonzero-pivot, and inverse hypotheses, the determinant of the matrix with rows $v$ followed by $R$ is the first entry of $v$ modulo $p$ times the determinant of the matrix formed by eliminating that pivot from each row in $R$.

**Proof.** Let $M$ be the matrix with first row $v$ and then the rows of $R$, and let $a$ be the residue of the first entry of $v$. Subtract from each row after the first its first-column entry times $a^{-1}$ times the first row; leave the first row unchanged. Adding multiples of one row to another preserves the determinant, so the resulting matrix $B$ has the same determinant as $M$. By the inverse hypothesis, every entry of the first column below $a$ is zero. Expanding along that column therefore gives $\det M=a$ times the determinant of the lower-right minor. Its entries are those of the rows obtained by eliminating the pivot: the tail coordinates are adjusted by subtracting the row's first entry times the inverse pivot times the corresponding pivot-row coordinate, all modulo $p$. The list access identities (`getD_tail`, `getD_zero_eq_headD`, and `getD_zipWith`) identify these coordinates with the definition of `elimRow`; the prime-modulus reduction identity (`natCast_sub_mod`) ensures the natural-number modular formula represents that subtraction in $\bbr/p\bbr$. The lower-right minor is consequently the matrix represented by the eliminated rows, proving the formula.

**Key facts.** `Complexity.BinArith.getD_tail`, `Complexity.BinArith.getD_zero_eq_headD`, `Complexity.BinArith.getD_zipWith`, `Complexity.BinArith.natCast_sub_mod`.
