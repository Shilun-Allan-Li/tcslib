<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satReduction_fallback -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reduction on Parse Failures

**Claim.** For every Boolean word $x$, if the exact CNF parser fails on $x$, then the string-level reduction of $x$ is the serialization of the empty CNF formula.

**Proof.** When parsing fails, decoding uses the fallback formula, which is the empty CNF. The reduction therefore transforms the empty formula. By the defining recursion of the transformation, starting from the empty formula produces the empty formula; serializing this result gives the claimed output.
