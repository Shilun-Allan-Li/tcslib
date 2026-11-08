<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.count_ofFn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counts in an indexed list

**Claim.** The number of occurrences of $a$ in the list of values of $f$ equals the number of indices $i<n$ for which $f(i)=a$.

**Proof.** Use the prefix-count formula for indexed lists (List.count_take_ofFn) with prefix length $n$. Every index in the domain satisfies $i<n$, so the prefix is the entire list and the condition $i<n$ adds no restriction to the filtered set. Thus the count is precisely the number of indices whose value is $a$.

**Key facts.** `List.count_take_ofFn`.
