<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix.lean :: Complexity.KarpLipton.transduce_drop_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity Action from the True State

**Claim.** For every finite binary string $p$, the transducer started in the true state outputs $p$ unchanged.

**Proof.** Induct on the length of $p$. The empty string produces the empty output. For $p=b::r$, the true state emits the current bit $b$, and its transition remains in the true state. By the induction hypothesis the remaining string $r$ is then emitted unchanged. The combined output is therefore $b::r=p$.
