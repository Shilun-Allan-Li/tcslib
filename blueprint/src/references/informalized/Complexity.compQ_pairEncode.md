<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compQ_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transformation on encoded queries

**Claim.** Applying the transformation to the encoding of $(x,\operatorname{bin}(i))$ returns the encoding of $(f(x),\operatorname{bin}(i))$.

**Proof.** The pair encoding decodes back to $(x,\operatorname{bin}(i))$ by `pairDecode_pairEncode`. The value of the binary expansion of $i$ is $i$ (`bitsVal_bits`), so the transformation’s canonicality check succeeds: the binary expansion of that value is again $\operatorname{bin}(i)$. Its definition therefore returns the encoding of $(f(x),\operatorname{bin}(i))$.

**Key facts.** `Turing.pairDecode_pairEncode`, `Complexity.LogProg.bitsVal_bits`.
