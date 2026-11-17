<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.serial_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serial Subtraction Value Identity

**Claim.** For inputs of length at most $N$, serial subtraction satisfies $\operatorname{val}(o)+\operatorname{val}(b)+c=\operatorname{val}(a)+2^N c_N$, where $o$ and $c_N$ are the output and final borrow.

**Proof.** Induct on the number $N$ of positions. At zero positions the length bounds make both strings empty, and direct evaluation gives the identity for either initial borrow. For the successor step, let $x,y$ be the current bits, using zero for a missing bit. The one-bit subtraction rule states that the output bit, the subtrahend bit, and the incoming borrow sum to the minuend bit plus twice the outgoing borrow. Apply the induction hypothesis to the dropped tails, initialized with that outgoing borrow. Decompose each input and the output into its head bit plus twice its tail value using Complexity.BinArith.bitsVal_eq_headD. Combining these identities, and using the successor formula for powers of two, yields the stated value identity.

**Key facts.** `Complexity.BinArith.bitsVal_eq_headD`.
