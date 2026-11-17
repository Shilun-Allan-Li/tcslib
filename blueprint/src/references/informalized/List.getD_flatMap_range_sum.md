<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_flatMap_range_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lookup with varying block lengths

**Claim.** In the concatenation of $f(0),\ldots,f(n-1)$, the entry at the sum of the lengths of the blocks before $f(r)$, plus $o$, is the entry at position $o$ in $f(r)$, provided $r<n$ and $o<|f(r)|$.

**Proof.** Because $r<n$, write $n=r+(c+1)$ for some natural number $c$. Split the range of indices at $r$: the concatenation consists of the blocks before $r$, followed by $f(r)$ and the blocks after it. The first part has length equal to the sum of the lengths of $f(0),\ldots,f(r-1)$ (`List.length_flatMap`). The append lookup rule says that looking up at this length plus an offset reduces to looking up at that offset in the remaining concatenation (`List.getD_append_add`). Splitting off the block $f(r)$ once more, the assumption $o<|f(r)|$ ensures the lookup lands in that block, where it is precisely its entry at $o$.

**Key facts.** `List.getD_append_add`.
