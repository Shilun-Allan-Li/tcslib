<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPRun.lean :: Randomized.PIT.gateRun_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded Gate Evaluation

**Claim.** The gate-running procedure on the encoded context and word $G$ returns the encoding of that context together with the state obtained after $|G|$ abstract evaluation steps from $(G,[])$.

**Proof.** Unpack the initial encoding: the initialized state is the pair encoding of $G$ and the encoded state for the specified context, word $G$, and empty value list. The bounded loop on such a pair removes the first component one bit at a time and applies its step function to the second; its defining property gives the result as the pair encoding of the empty word and the iterated step applied $|G|$ times (`forLoop_pairEncode`). Projecting the second component recovers that iterated result (`pairSndD_pairEncode`). Finally, iterating the encoded evaluator step agrees with iterating the abstract evaluator step for the same number of times (`iterate_gStep`), yielding the stated encoding.

**Key facts.** `Complexity.BinArith.forLoop_pairEncode`, `Complexity.pairSndD_pairEncode`, `Randomized.PIT.iterate_gStep`.
