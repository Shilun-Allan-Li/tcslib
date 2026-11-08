<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.sum_hammingBallRademacherSummand -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum of Normalized Sign Summands

**Claim.** For every $n$ and sign vector $x$, the sum of the normalized coordinate sign summands equals the linear form with every coefficient equal to $1/\sqrt n$.

**Proof.** By definition, each coordinate summand is the normalized coefficient $(\sqrt n)^{-1}$ multiplied by the sign value at that coordinate. The normalized sum is the linear form whose coefficient at every coordinate is the same $(\sqrt n)^{-1}$. The two expressions therefore agree term by term.
