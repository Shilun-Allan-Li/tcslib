<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.inWin_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run stays within the space window

**Claim.** If every run uses at most $sp(|x|)$ space and $sp(|x|)\le s$, then every choice-word run on $x$ has all work-tape heads within distance $s$ and all cells outside that window blank.

**Proof.** The global space hypothesis applied to input $x$ and word $w$ bounds the space used along that run by $sp(|x|)$, hence by $s$. The run-prefix window lemma (`runWith_take_inWindow`) says that every prefix configuration, including the prefix of length $|w|$ that is the full run, has its work-tape heads within distance $s$ and its cells outside that range blank. This is exactly the asserted window condition.

**Key facts.** `Turing.NDTM.runWith_take_inWindow`.
