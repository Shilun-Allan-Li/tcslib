<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipWork -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Work-Field Skipping

**Claim.** The work-field skipper that consumes an arbitrary two-bit pair followed by a two-bit pair other than $01$ is primitive recursive.

**Proof.** The first pair is consumed by the pair skipper with the validity test that always accepts. Bind its remaining suffix to a second pair skipper, whose validity condition accepts precisely when the pair is not $01$. Primitive-recursive functions are closed under option-valued binding and composition, so the resulting work-field skipper is primitive recursive.

**Key facts.** `Turing.codePrimSkipPair`.
