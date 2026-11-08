<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: BooleanAnalysis.chiS_flipBit_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh character under a bit flip

**Claim.** Flipping coordinate $i$ changes the Walsh character $\chi_S$ by a factor of $-1$ when $i\in S$, and leaves it unchanged when $i\notin S$.

**Proof.** The proof invokes the established bit-flip identity for Walsh characters (`chiS_flipBit`), which states exactly these two cases. Applying it to $S$, $x$, and $i$ yields the claimed formula.

**Key facts.** `BooleanAnalysis.chiS_flipBit`.
