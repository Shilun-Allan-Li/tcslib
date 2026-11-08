<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Compat.lean :: List.map_coe_finRange_eq_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite range as a natural-number range

**Claim.** Mapping each element of the finite range of size $n$ to its underlying natural number gives the list of natural numbers from $0$ through $n-1$.

**Proof.** The finite range enumerates the elements of $\mathrm{Fin}(n)$ in order. Taking each element's underlying natural number therefore produces, in order, precisely the natural numbers below $n$, which is `List.range n`.
