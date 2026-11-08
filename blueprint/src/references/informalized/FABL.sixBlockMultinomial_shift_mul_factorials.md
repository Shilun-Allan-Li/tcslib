<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.sixBlockMultinomial_shift_mul_factorials -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Six-Block Factorial Identity

**Claim.** For all nonnegative integers $m,d$, the six-block multinomial coefficient with six parts of size $d$ and one part of size $m$, multiplied by $(d!)^6m!$, equals $(m+6d)!$.

**Proof.** Let the seven part sizes be $d$ for the first six positions and $m$ for the last. Their sum is $m+6d$, and the product of their factorials is $(d!)^6m!$. The multinomial factorial identity (`Nat.multinomial_spec`) says that the multinomial coefficient for these parts times this product equals the factorial of their sum. In the definition of the six-block coefficient at total size $m+6d$, the final part is $(m+6d)-6d=m$, so that coefficient is exactly the one in this identity. Rearranging gives the result.
