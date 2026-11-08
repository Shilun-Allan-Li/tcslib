<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitter_take_succ_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Extended Word Prefixes

**Claim.** The prefixes of $u$ and $v$ of length $j+1$ agree exactly when their prefixes of length $j$ agree and their optional entries at index $j$ agree.

**Proof.** If the length-$(j+1)$ prefixes are equal, taking their first $j$ entries gives equality of the length-$j$ prefixes. Looking at index $j$ in the equal prefixes gives equality of the optional entries there. Conversely, each length-$(j+1)$ prefix is its length-$j$ prefix followed by the optional entry at index $j$. The two assumed equalities therefore make these extended prefixes equal.
