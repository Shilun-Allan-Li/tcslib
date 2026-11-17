<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codePrimRepeat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of Counted Iteration

**Claim.** If a reader is jointly primitive recursive in its parameter and input string, and the iteration count is primitive recursive in the parameter, then repeatedly applying that reader the specified number of times, passing each returned suffix onward and propagating failure, is jointly primitive recursive.

**Proof.** Write each application as the option-valued operation that binds a current result to the reader: a successful suffix is passed to the next step, while failure remains failure. Starting from the input string wrapped as a successful option, iterate this operation as many times as the primitive recursive count prescribes. The initial option-valued input is primitive recursive, and the step is primitive recursive by the hypothesis on the reader together with option bind. Natural-number iteration with a primitive recursive iteration count is primitive recursive. The identity codeSkipRepeat_iter identifies this iterate with the stated repeated-reader operation, proving the claim.

**Key facts.** `Turing.codeSkipRepeat_iter`.
