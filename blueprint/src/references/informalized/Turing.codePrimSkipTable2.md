<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimSkipTable2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Two-Tape Table Skipper

**Claim.** For every natural number $n$, the two-tape table skipper that processes $n+1$ rows is primitive recursive jointly in $n$ and its Boolean-string input.

**Proof.** The action-field skipper for two work tapes is primitive recursive. Apply the primitive-recursive repetition construction three successive times with constant count $3$, and then a fourth time with count $n+1$. The nested repetitions give the specified three groups of three fields per row, repeated for all $n+1$ rows. The repetition theorem preserves primitive recursiveness when its count is a primitive-recursive function, and $n\mapsto n+1$ is primitive recursive.

**Key facts.** `Turing.codePrimSkipActionK`, `Turing.codePrimRepeat`.
