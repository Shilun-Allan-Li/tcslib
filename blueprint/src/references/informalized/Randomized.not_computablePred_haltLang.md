<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.not_computablePred_haltLang -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Undecidability of the Halting Language

**Claim.** The language defined using the specified transducers, the recursively encoded halting prefix, and membership in the halting set is not computable.

**Proof.** Assume for contradiction that membership in the halting language is computable, and let $D$ be a procedure deciding it. First, the maps sending $n$ to a list of $n$ true bits and $j$ to $4^{j+1}$ are computable, by primitive recursion. The specified query string is formed by concatenating such a list with a false bit followed by another repeated-true list. It is therefore computable from its two natural-number inputs.

Now define a computable update on a pair $(j,v)$ by sending it to $4v$ plus the bit returned by applying $D$ to the query string built from $v$ and $j$. Recursion on $j$, starting at zero and applying this update with the current prefix value, computes the halt prefix. To see that this recursion has the intended values, use the query characterization (`Randomized.hlQuery_mem_iff`): the query built from the true halt prefix at stage $j$ belongs to the halting language exactly when $j$ is in the halting set. Thus $D$ returns the halting digit at each stage, and the update agrees with the defining recurrence for the halt prefix.

Finally, given $j$, compute this prefix and feed the corresponding query string to $D$. By the same characterization, the answer decides whether $j$ belongs to the halting set. This would make the halting digit predicate computable, contradicting its undecidability (`Randomized.not_computablePred_haltDigit`). Therefore membership in the halting language is not computable.

**Key facts.** `Randomized.hlQuery_mem_iff`, `Randomized.not_computablePred_haltDigit`.
