<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_fuel_bits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Digits of a Mersenne Number

**Claim.** For every natural number $w$, the binary digit list of $2^w-1$ consists of exactly $w$ true entries.

**Proof.** Induct on $w$. At $w=0$, the number is zero and its digit list is empty, matching the zero-fold repetition of true. For the successor, use $2^{w+1}-1=2(2^w-1)+1$. The binary expansion rule for an odd number of the form $2n+1$ places a true bit first and then gives the bits of $n$ (`Nat.bit1_bits`). By the induction hypothesis those remaining bits are $w$ true entries, so the full list has $w+1$ true entries.
