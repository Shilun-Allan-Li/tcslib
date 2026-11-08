<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.CodeAt.left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left Part of a Code Segment

**Claim.** If $l_1\mathbin{++}l_2$ is a prefix of the part of $P$ beginning at position $\mathrm{pos}$, then $l_1$ is also a prefix of that part.

**Proof.** The list $l_1$ is a prefix of $l_1\mathbin{++}l_2$. Prefix relations compose, so from this fact and the assumed prefix relation of $l_1\mathbin{++}l_2$ into the part of $P$ beginning at $\mathrm{pos}$, we obtain that $l_1$ is a prefix of that part.
