<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPReduce.lean :: Randomized.PIT.length_uHead_add_uRest_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Combined transducer length bound

**Claim.** For every bit string $w$, the lengths of the two specified transducer outputs sum to at most $|w|$.

**Proof.** Proceed by induction on $w$. The empty word gives two empty outputs. For a word $b::w$, consider its first bit. If $b$ is true, the first transducer outputs that bit and continues on the tail in its active state; the second outputs nothing at this bit and continues in its initial state. The induction hypothesis bounds the sum of the tail outputs by $|w|$, so adding the one emitted bit gives at most $1+|w|$. If $b$ is false, the first transducer emits nothing and remains inactive on the tail, while the second emits nothing at this bit and switches to the state that passes through the tail. The first output on the tail is empty, and the second has length at most $|w|$, so their sum is at most $1+|w|$.
