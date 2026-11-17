<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.serial_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serial Binary Addition

**Claim.** For inputs of length at most $N$, the output bits and final carry of the serial addition procedure encode the sum of the input values and initial carry.

**Proof.** Proceed by induction on the number $N$ of processed positions. When $N=0$, the length bounds force both input strings to be empty; the output is empty and the state remains the initial carry, giving the identity directly. For the step from $N$ to $N+1$, let $x,y$ be the current least significant bits, taking a missing bit to be zero. The one-bit addition rule says that the output bit plus twice the next carry equals $x+y$ plus the incoming carry. The remaining positions are precisely the dropped tails of the inputs, and their lengths are at most $N$. Apply the induction hypothesis to those tails with the updated carry. The binary-value decomposition into head bit plus twice the value of the tail (Complexity.BinArith.bitsVal_eq_headD), together with $2^{N+1}=2\cdot2^N$, combines the one-position identity with the tail identity to give the claimed formula.

**Key facts.** `Complexity.BinArith.bitsVal_eq_headD`.
