<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/MergeSort.lean :: Light.MergeSort.time_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Merge Sort Time Split Bound

**Claim.** For every natural number $n\ge2$, the costs $61n+70$ and the two recursive time bounds at the split sizes sum to at most $\mathrm{sortTime}(n)$.

**Proof.** By `clog_split`, the sum of the two split-size logarithmic contributions, plus $n$, is at most $n\operatorname{clog}_2(n)$. Expand $\mathrm{sortTime}$ in the claimed inequality. The shared linear terms and constants reduce the remaining comparison to this logarithmic bound: the two recursive logarithmic terms together with $n$ are bounded by the full-size logarithmic term. Thus the stated total cost is at most $\mathrm{sortTime}(n)$.

**Key facts.** `Light.MergeSort.clog_split`.
