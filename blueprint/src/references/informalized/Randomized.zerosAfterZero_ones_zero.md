<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/QuasiPolyHierarchy.lean :: Randomized.zerosAfterZero_ones_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output After a Zero

**Claim.** For every natural number $j$ and every finite Boolean string $l$, the transducer produces a string of $|l|$ zeros on the concatenation of $j$ ones, a zero, and $l$.

**Proof.** Induct on $j$. When $j=0$, the input begins with zero, so the transducer enters the state recording that it has seen a zero. From then on it emits one zero for each bit of $l$; the fact that this output is a string of $|l|$ zeros is the already established behavior of the transducer after it has seen a zero (`Randomized.transduce_seen`). For the successor case, the input starts with one more initial one. That bit emits nothing and leaves the machine in its initial state, so the output reduces to the induction-hypothesis case for the remaining $j$ ones, the zero, and $l$.

**Key facts.** `Randomized.transduce_seen`.
