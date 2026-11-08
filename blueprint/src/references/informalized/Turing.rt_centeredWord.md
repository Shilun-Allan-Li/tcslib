<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.rt_centeredWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Boolean Word Identity

**Claim.** For any function $f$ on Boolean values, mapping $f$ over the values of the test $j=s$ for $j=0,\ldots,2s$ gives the list obtained by applying $f$ to $s$ false values, then true, then $s$ false values.

**Proof.** The two lists have the same length, namely $2s+1$, so it suffices to compare entries at each index $j$. If $j<s$, the test $j=s$ is false, and the entry lies in the initial block of $s$ false values. If $j=s$, the test is true and the entry is the single central true value. If $j>s$, the test is false and the entry lies in the final block of $s$ false values. Thus the entries agree at every index, proving equality of the lists.
