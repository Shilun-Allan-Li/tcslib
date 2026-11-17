<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Div.lean :: Complexity.BinArith.divLoop_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient and remainder of the division loop

**Claim.** When the second projection of $z$ has positive value, the division loop's quotient and remainder projections have values equal to the integer quotient and remainder of the first projection's value divided by the second projection's value.

**Proof.** The invariant holds initially (`divInv_init`) and is preserved by every step (`divInv_step`), so it holds after the prescribed number of iterations (`iterate_invariant`). Measure the pending prefix by its length. Each step strictly decreases this measure whenever it is positive, and a state with measure zero is fixed (`divInv_step`); the general iteration principle therefore shows that the chosen iteration count leaves the pending prefix empty (`iterate_measure_eq_zero`). The count suffices because the initial pending prefix has length at most the input length, by `length_pairFstD_le`. Unpacking the invariant at this terminal state gives $R=[]$. The invariant's value equation consequently reduces to $qv+r=a$, and its bound gives $r<v$, where $a$ and $v$ are the values of the first and second projections. Since $v>0$, uniqueness of quotient and remainder identifies $q=a/v$ and $r=a\%v$. The encoded-state projection identities (`pairFstD_pairEncode`, `pairSndD_pairEncode`) identify these with the stated nested projections.

**Key facts.** `Complexity.BinArith.divInv_init`, `Complexity.BinArith.divInv_step`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.length_pairFstD_le`, `Complexity.BinArith.iterate_invariant`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`.
