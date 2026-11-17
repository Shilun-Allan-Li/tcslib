<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Stored_exact -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Stored Instance and Round

**Claim.** For every stated choice of machine, constants, cursor, and input word, the packed word stores exactly $x$ as its instance, and its stored last-round index is $\operatorname{clLastRound}(|x|,M.k,\operatorname{clProducerHorizon}(C,e,c,A,d,|x|))$.

**Proof.** Expand the definitions of the packed word, its stored header, instance, and round. Each nested pair encoding is recovered exactly by the pair-decoding identity (\texttt{Turing.pairDecode\_pairEncode}). Thus the stored instance field reduces to $x$. The stored round uses the length of the decoded instance and the length of the decoded horizon field; these are respectively $|x|$ and the producer horizon at input length $|x|$. Substitution yields the claimed last-round expression.

**Key facts.** `Turing.pairDecode_pairEncode`.
