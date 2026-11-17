<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.pathOr_bit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indexed bit test

**Claim.** On the paired encoding of $x$ and the binary representation of $i$, the indicator of the indexed bit-test language equals $x.getD\ i\ false$.

**Proof.** The paired-encoding indicator formula (`Complexity.indicator_indexLang_pairEncode`) says that evaluating the indicator of an indexed language on this encoding returns the Boolean decision of its defining predicate at $(x,i)$. For the bit-test language that predicate is $x.getD\ i\ false = true$. Its Boolean decision is exactly the Boolean value $x.getD\ i\ false$, giving the claimed equality.

**Key facts.** `Complexity.indicator_indexLang_pairEncode`.
