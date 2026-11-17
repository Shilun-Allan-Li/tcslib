<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.CfgTableau.optOf_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# False Flag Gives No Value

**Claim.** For every Boolean $v$, using the false presence flag in the optional-Boolean construction gives `none`.

**Proof.** By definition, the construction returns `some v` only when its flag is true. With the flag false, it takes the other branch and returns `none`.
