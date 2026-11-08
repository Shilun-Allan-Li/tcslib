<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Checks.lean :: Complexity.Codec.inputSymbol_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Symbol from Head Position

**Claim.** For a configuration on Boolean input $x$, the input symbol read by its head is absent at positions $0$ and $|x|+1$, and otherwise is the symbol at index $p-1$, with false as the default if that index is out of range.

**Proof.** Let $p$ be the value of the input-head position. If the position itself is zero, both the configuration's input-symbol function and the stated position-based function return no symbol. If instead $p=|x|+1$, the bound that the position is a valid element of $\mathrm{Fin}(|x|+2)$ identifies it with the right-end position; again both functions return no symbol. In the remaining case, $p$ is neither endpoint. The same finiteness bound then implies $p-1<|x|$, so the configuration's indexed input symbol exists and equals the list entry at index $p-1$. Expressing that entry as an option-valued lookup with default false gives exactly the stated function.
