<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityRealRoot_le_blockSide -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real root bounded by block side

**Claim.** For natural numbers $n$ and $h$, if $r=n^{1/h}$ and $b$ is the larger of $1$ and the least natural number greater than or equal to $r$, then $r\le b$.

**Proof.** The real number $r$ is at most its natural ceiling. By definition, $b$ is the maximum of $1$ and that ceiling, so it is at least the ceiling. Combining these inequalities gives $r\le b$.
