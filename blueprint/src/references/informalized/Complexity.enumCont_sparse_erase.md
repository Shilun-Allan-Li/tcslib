<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_sparse_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erasing the Last Sparse Cell

**Claim.** For a finite list $w$ of possibly blank Boolean cells and a possibly blank cell $b$, blanking cell $|w|$ of the sparse tape encoded by $w$ followed by $b$ yields the sparse tape encoded by $w$.

**Proof.** The sparse tape for $w$ followed by $b$ is the tape for $w$ with its cell at position $|w|$ updated to $b$ (the append description of the sparse tape, `Complexity.enumCont_sparse_append`). Updating that same position to blank therefore makes the two updates idempotent: the resulting tape is the tape for $w$ with its cell at position $|w|$ set to blank. But the tape for $w$ is already blank at position $|w|$, since that position is outside the list. Updating it there changes nothing, so the resulting tape is exactly the tape for $w$.

**Key facts.** `Complexity.enumCont_sparse_append`.
