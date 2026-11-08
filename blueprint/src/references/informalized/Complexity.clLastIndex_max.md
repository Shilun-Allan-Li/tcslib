<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLastIndex_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Last Match as a Filtered Maximum

**Claim.** The last index below $n$ where $P$ is true, or no value if there is none, equals the maximum of the indices below $n$ where $P$ is true, with the maximum undefined for an empty set.

**Proof.** Induct on $n$. At $n=0$, both sides are undefined. For the successor step, separate whether $P(n)$ is true. If it is, the filtered range consists of the earlier matches together with the new, largest index $n$, so its maximum is $n$; the last-match tracker also returns $n$. If $P(n)$ is false, filtering the appended index adds nothing, and the tracker retains its value from the length-$n$ case. The induction hypothesis therefore gives equality in this case as well.
