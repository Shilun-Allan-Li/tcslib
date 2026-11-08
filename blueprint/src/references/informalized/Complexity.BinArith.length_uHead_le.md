<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.length_uHead_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary head output length bound

**Claim.** For every bit string $w$, the unary head transducer's output on $w$ has length at most $|w|$.

**Proof.** Proceed by induction on $w$. The empty input produces empty output. For a nonempty input $b::w$, split on the first bit. If $b$ is false, the output is empty, so the bound holds. If $b$ is true, the output is a leading true bit followed by the output on $w$; this is the characterization of the unary head on a true initial bit (`uHead_true_cons`). The induction hypothesis bounds the tail output by $|w|$, so the total length is at most $1+|w|=|b::w|$.

**Key facts.** `Complexity.BinArith.uHead_true_cons`.
