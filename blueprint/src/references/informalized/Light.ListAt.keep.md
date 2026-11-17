<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/ArrayAt.lean :: Light.ListAt.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving a Recorded List Under Agreement

**Claim.** If two functions agree at every index in the recorded segment, then a list recording that segment for the first function also records it for the second, with its length and endpoint bound unchanged.

**Proof.** Keep the original list length and endpoint bound. For each position $i$ in the list, the recorded index $a+i$ lies in the segment from $a$ to $a+N$ and below $\mathrm{top}$, by the length and endpoint hypotheses. The functions therefore agree at that index. Replacing each recorded value using this agreement shows that the same list records the segment for $\mu'$ (`Seg.congr`).

**Key facts.** `Light.Seg.congr`.
