<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: Light.AbsLe.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Bounds Under Concatenation

**Claim.** If every entry of each of two integer lists has absolute value at most $U$, then every entry of their concatenation also has absolute value at most $U$.

**Proof.** An entry of a concatenation belongs to one of its two constituent lists. In the first case its bound follows from the hypothesis for the first list, and in the second case from the hypothesis for the second. Therefore every entry of the concatenation has absolute value at most $U$.
