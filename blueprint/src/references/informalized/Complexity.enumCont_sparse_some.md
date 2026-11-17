<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_sparse_some -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sparse Tape of a Boolean Word

**Claim.** For every finite Boolean word $w$, the sparse tape obtained by replacing every symbol of $w$ with a nonblank cell containing that symbol is the buffer tape storing $w$.

**Proof.** Check the two tapes pointwise. At a nonnegative integer position, both use the list entry at the corresponding natural-number index. Mapping each Boolean symbol to its nonblank cell and then reading that cell returns the original symbol; if the index is beyond the end of the word, both readings are blank. At a negative position, both tapes are blank by definition. Hence they agree everywhere.
