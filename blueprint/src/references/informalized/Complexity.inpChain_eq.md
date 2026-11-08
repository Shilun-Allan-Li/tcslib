<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.inpChain_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Chain Recurrence

**Claim.** For a binary input $w$, time $t$, and position $p$, the input-chain value equals the input symbol at $p$ when the head is at $p$; otherwise it is empty at $p=0$, and at positive $p$ it equals the input-chain value at $p-1$.

**Proof.** The input symbol of a configuration is the input bit at its head position (`inputSymbol_eq_inputBitAt`). Unfolding the input-chain definition, first consider whether the head position equals $p$. If so, the chain condition that the head position is at most $p$ holds, and the chain value is the input symbol, which is the bit at position $p$. If the head is not at $p$, the chain is empty when the head lies to the right of $p$. For the stated recurrence, split further on whether $p=0$: at zero the right-hand side is empty, while for positive $p$, the head position is at most $p$ exactly when it is at most $p-1$ (given it is not $p$). In that latter case the chain agrees with its value at $p-1$; otherwise both sides are empty.

**Key facts.** `Complexity.inputSymbol_eq_inputBitAt`.
