<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/RadixPass.lean :: Light.radixPass_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radix Pass Execution

**Claim.** Given the stated preconditions for a radix pass, valid program entries for counting sort and copying, and the required depth and time bounds, the radix-pass program finishes within time $T$. Its only change to the local variables is at the unused-variable position, and its resulting memory satisfies the radix-pass postcondition: it agrees with the initial memory outside the designated region, has the specified bucket starting counts, and contains a stable permutation sorted by the keys.

**Proof.** The precondition for the radix pass supplies the precondition needed to run counting sort (`Light.RadixPass.Pre.sort`). First call the counting-sort procedure on the input permutation and key data. The counting-sort specification (`Light.countSort_meets`) yields the bucket-prefix counts and a stably ordered list of indices in its output memory. The argument expressions are safe and evaluate to the required parameters by the given expression-value hypotheses; the word bound and address facts ensure the memory operations are valid. The call-composition rule (`Light.Ends.callThen`) combines this first call with the remaining copy step, respecting the depth and total-time bounds. Then call the copying procedure to move the ordered list from the scratch segment back to the designated permutation segment. Its specification (`Light.copy_meets`) gives the copied entries and ensures that the copy changes no memory outside its destination segment. Finally, the sorted-and-copied characterization (`Light.RadixPass.Post.of_sorted_copied`) combines the counting-sort output and copy guarantees into the radix-pass postcondition. The call rule (`Light.Ends.callLast`) accounts for this final procedure call; the call wrappers update the unused local variable as stated, and the supplied cost bound ensures the total execution time is at most $T$.

**Key facts.** `Light.RadixPass.Pre.sort`, `Light.countSort_meets`, `Light.Ends.callThen`, `Light.copy_meets`, `Light.RadixPass.Post.of_sorted_copied`, `Light.Ends.callLast`.
