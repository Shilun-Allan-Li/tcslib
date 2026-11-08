<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.pathOr_len -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed length test

**Claim.** On the paired encoding of $x$ and the binary representation of $i$, the indicator of the indexed length-test language is true exactly when $i<x.length$.

**Proof.** The paired-encoding indicator formula (`Complexity.indicator_indexLang_pairEncode`) evaluates the indicator by deciding the language's defining predicate at $(x,i)$. For the length-test language that predicate is $i<x.length$, so its decision is precisely $\mathrm{decide}(i<x.length)$, as asserted.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
