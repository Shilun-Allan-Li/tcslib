<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipTable1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the One-Tape Table Skipper

**Claim.** The two-input skip-table function associated with the one-tape code format is primitive recursive.

**Proof.** The one-tape action skipper is primitive recursive: specialize the primitive-recursiveness result for action skippers to one work tape, using the equality identifying the general action skipper with this specialization. Apply the primitive-recursive repetition construction three times with constant count $3$, then once more with count $n+1$. The resulting function skips three groups of three fields for each of the $n+1$ rows, which is the one-tape table skipper.

**Key facts.** `Turing.codePrimSkipActionK`, `Turing.codeSkipAction_eq_codeSkipActionK`, `Turing.codePrimRepeat`.
