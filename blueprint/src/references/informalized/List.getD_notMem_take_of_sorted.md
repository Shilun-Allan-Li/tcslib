<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.getD_notMem_take_of_sorted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A new value outside the preceding prefix

**Claim.** In a nondecreasing finite list, if the entry at index $i$ is either the first entry or differs from its predecessor, then it does not occur among the first $i$ entries.

**Proof.** Suppose the entry at index $i$ occurs in the first $i$ entries, say at some index $j<i$. If $i=0$, this is impossible because no index is less than zero. Otherwise, the sortedness condition gives $l[j]\le l[i-1]\le l[i]$. The first inequality follows from pairwise sortedness when $j<i-1$, and is equality when $j=i-1$. Since the assumed occurrence says $l[j]=l[i]$, antisymmetry forces $l[i-1]=l[i]$, contradicting the hypothesis that these consecutive entries differ.
