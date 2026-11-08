<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamBound_size -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Size Bound for Encoded Seam Words

**Claim.** If the consumed length of a seam state is at most $|x|$ and its fresh-variable cursor is at most $|x|$ plus its consumed length, then the cursor is at most $2|x|$ and its encoded seam word has length at most $6|x|+8$.

**Proof.** Let $u$ be the consumed length, $f$ the fresh-variable cursor, and $p$ the phase value. The hypotheses give $u\le |x|$ and $f\le |x|+u$, while the phase field gives $p<5$. The encoding-length identity ($\texttt{satStreamWord_length}$) states that the word length is $2f+2u+p+4$. First, $f\le |x|+u\le 2|x|$. Substituting the bounds into the length identity gives $2f+2u+p+4\le 4|x|+2|x|+4+4=6|x|+8$, proving both estimates.

**Key facts.** `Complexity.satStreamWord_length`.
