<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/DetMod.lean :: Complexity.BinArith.cInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation and Progress of Determinant Elimination

**Claim.** A determinant-elimination step preserves the stated invariant. When the measure is positive, the measure strictly decreases; when the measure is zero, the step leaves the state unchanged.

**Proof.** Write the state as $(R,d,m,r)$, where $R$ is the row list and $r$ is the row counter. The invariant gives $|R|=m$. Primality ensures $p\ge2$, so the step's exceptional case $p<2$ cannot occur. If $R$ is empty, then $m=0$; the step fixes the state. The measure is then $-r$, which can be zero only when $r=0$ and is never positive, giving the required progress and zero-measure conclusions.

Now suppose $R$ is nonempty, so $m=|R|>0$. In particular, the measure $m(m+2)-r$ is nonzero, since $r\le m$ and $m<m(m+2)$. If $m\le r$, the step resets the state to the empty zero state. The invariant says every row has zero first entry, so the represented matrix has a zero first column and determinant zero (`det_matOfRows_eq_zero`). The determinant invariant therefore still holds after the reset. The new measure is zero, strictly below the old positive measure, and the old measure was not zero.

In the remaining cases $r<m$. If the first entry of the first row is zero, the step moves that row to the end and increments $r$. Row dimensions and entry bounds are unchanged, and the increment preserves $r\le m$. The condition on the last $r+1$ rows follows from the old condition on the last $r$ rows, together with the moved row's zero first entry. The determinant changes by the sign $(-1)^{m-1}$ under this row rotation (`det_matOfRows_rotate`); the accumulator is multiplied by $p-1$ exactly when $m$ is even. Since $p-1$ represents $-1$ modulo $p$, this adjustment compensates for the rotation sign, preserving the determinant invariant. The measure decreases by one, and the old measure is nonzero.

Finally, suppose the first row has nonzero first entry. It is nonempty, so write it as a pivot $a$ followed by its tail. The entry bounds give $a<p$, and the nonzero condition ensures that $a$ is nonzero modulo the prime $p$. Fermat's theorem in the form `natCast_pow_mod_eq_inv` identifies $a^{p-2}$ modulo $p$ with the inverse of $a$. The elimination determinant formula (`det_matOfRows_elim`) then says the old determinant is $a$ times the determinant of the matrix formed from the eliminated remaining rows. Multiplying the accumulator by $a$ modulo $p$ preserves the invariant. The eliminated rows have the required common length (`length_elimRow`) and their entries remain below $p$ (`lt_of_mem_elimRow`); the row counter is reset to zero, so the trailing-zero condition is vacuous. The new dimension is $m-1$, and its measure is $(m-1)(m+1)$, strictly below $m(m+2)-r$ using $r\le m$. Again the old measure is nonzero. These cases establish all three assertions.

**Key facts.** `Complexity.BinArith.det_matOfRows_eq_zero`, `Complexity.BinArith.det_matOfRows_rotate`, `Complexity.BinArith.det_matOfRows_elim`, `Complexity.BinArith.length_elimRow`, `Complexity.BinArith.lt_of_mem_elimRow`, `Complexity.BinArith.natCast_pow_mod_eq_inv`.
