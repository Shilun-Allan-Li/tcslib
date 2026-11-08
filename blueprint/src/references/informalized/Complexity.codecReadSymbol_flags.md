<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecReadSymbol_flags -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of a Boolean symbol

**Claim.** For every optional Boolean symbol $v$, the flags indicating whether it is respectively the present symbol false or the present symbol true recover $v$.

**Proof.** If $v$ is absent, both flags are false and the reader returns none. If $v$ is present and false, the false flag alone is true, so the reader returns false. If $v$ is present and true, the true flag is true, so it returns true.
