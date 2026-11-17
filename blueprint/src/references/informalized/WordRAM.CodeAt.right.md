<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.CodeAt.right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Part of a Code Segment

**Claim.** If $l_1\mathbin{++}l_2$ is a prefix of the part of $P$ beginning at position $\mathrm{pos}$, then $l_2$ is a prefix of the part beginning at $\mathrm{pos}+|l_1|$.

**Proof.** Write the part of $P$ beginning at $\mathrm{pos}$ as $(l_1\mathbin{++}l_2)\mathbin{++}r$ for some remainder $r$. Dropping the first $|l_1|$ instructions from this suffix removes $l_1$, leaving $l_2\mathbin{++}r$. This is precisely the suffix of $P$ beginning at $\mathrm{pos}+|l_1|$, so $l_2$ is its prefix.
