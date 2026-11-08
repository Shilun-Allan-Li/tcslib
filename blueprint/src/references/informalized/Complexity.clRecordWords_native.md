<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRecordWords_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Recorder Input Assembly

**Claim.** If the word-valued function $y$ and the unary word encoding of $T$ are polynomial-time computable, then packing the recorder's initial tape words for $y(x)$ and $T(x)$, together with four empty fields, is polynomial-time computable.

**Proof.** List the finitely many initial tape fields as functions of the input word. For each field, split the tape layout into its cases: the recorder's blank fields and fixed buffers are constant words, the clock field is the given unary encoding of $T$, and the input field is $y$. Each constant field is polynomial-time computable by the constant-function construction (`computesFunInTime_const`) followed by the linear-time polynomial-time criterion (`clNative_linear`); the clock and input fields are polynomial-time computable by the assumptions. Thus every field function is polynomial-time computable. The closure result for self-delimiting field packing (`clNative_fields`) now shows that packing this finite list of fields is polynomial-time computable. The displayed list of field functions is precisely the recorder layout followed by four empty fields, yielding the desired function.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_linear`, `Complexity.clNative_fields`.
