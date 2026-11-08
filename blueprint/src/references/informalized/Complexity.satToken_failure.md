<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satToken_failure -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Token Suffix After Parse Failure

**Claim.** For every bit string $r$, if the literal parser fails on $1::r$, then splitting off its leading unary token leaves the empty suffix.

**Proof.** The shape theorem for the unary token split (satToken_shape) identifies its suffix as the tail after the initial run of true bits and the next delimiter bit. Let `takeTrues` applied to $r$ return $(k,y)$. If $y$ is empty, or begins with a false bit and has no further bit, the shape theorem shows directly that the split suffix of $1::r$ is empty. If $y$ begins with true, the shape theorem's assertion that the residual after removing the initial true run cannot begin with true rules this case out. In the remaining case, $y$ begins with false and has a following bit. The parser then sees a positive run of true bits, the false delimiter, and that following bit, so it succeeds—contradicting the assumed failure. Hence only the cases with empty split suffix remain.

**Key facts.** `Complexity.satToken_shape`.
