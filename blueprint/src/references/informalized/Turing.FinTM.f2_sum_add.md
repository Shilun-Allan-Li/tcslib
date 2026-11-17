<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_sum_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Addition of Finite Sums

**Claim.** For natural numbers $a,b$ and a function $f$ on the first $a+b$ indices, its sum over all those indices equals the sum over the first $a$ indices plus the sum over the remaining $b$ indices.

**Proof.** Reindex the indices of the full sum using the equivalence between the disjoint union of the first $a$ indices and the next $b$ indices, and the indices from $0$ through $a+b-1$. Reindexing preserves the sum. The sum over that disjoint union splits into the sum over each part (`Finset.sum_disjSum`), whose indices correspond respectively to $i\mapsto\mathrm{castAdd}(b,i)$ and $i\mapsto\mathrm{natAdd}(a,i)$.
