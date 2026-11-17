<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Padding.lean :: Complexity.PolyHierarchy.dropWhile_replicate_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping a false prefix

**Claim.** Deleting the initial false entries from a word consisting of $k$ false entries followed by true and then $r$ yields the word consisting of true followed by $r$.

**Proof.** Induct on $k$. When $k=0$, the word already begins with true, so dropping its false prefix leaves it unchanged. For the successor case, the word begins with one additional false followed by the word for $k$; dropping a false at the front reduces the calculation to the induction hypothesis, which leaves exactly true followed by $r$.
