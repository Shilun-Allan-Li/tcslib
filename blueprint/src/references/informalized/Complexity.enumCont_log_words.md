<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_log_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logging Preserves the Empty History Seam

**Claim.** For a Boolean machine with at least one work tape, logging the seam configuration with state $q$ and word $s$ on tape zero, using empty history, gives exactly the logging machine’s seam configuration with the same state and word.

**Proof.** Compare the configuration fields: state, input-head position, and output are unchanged by logging. For the work tapes, split the enlarged tape bank into the original tapes, the buffer tape, and the two history banks. On each original tape, the logged configuration agrees with the original one; the positive-tape assumption ensures that tape zero remains the unique tape carrying $s$. The buffer and history tapes are blank: the empty history makes each history tape a sparse encoding of a list of blanks, and the fact that sparse encoding a replicated list of blanks is identically blank supplies this conclusion (`enumCont_sparse_blanks`). The head positions also agree: the original heads are at zero, the buffer head is at the empty-history length zero, and both history banks have head position zero. Thus every field of the two configurations agrees.

**Key facts.** `Complexity.enumCont_sparse_blanks`.
