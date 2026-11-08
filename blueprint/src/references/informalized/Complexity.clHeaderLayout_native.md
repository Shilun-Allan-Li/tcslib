<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clHeaderLayout_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Recorder Layout

**Claim.** For every finite Turing machine $M$ over the Boolean alphabet, the function sending a Boolean word $z$ to the self-delimiting packing of the fields in its recorder layout is polynomial-time computable.

**Proof.** List the recorder-layout fields as functions of the input word, in their given order. Each field is polynomial-time computable: the constant empty fields are covered by constant-function computation, the two header fields by the polynomial-time field and tail results, and the retained fields by the corresponding field result. The layout cases simply select these fields according to the finite index decomposition. Thus every function in the list is polynomial-time computable. The polynomial-time closure result for packing a finite list of polynomial-time functions then shows that applying the field-packing operation to this list is polynomial-time computable.

**Key facts.** `Complexity.clHeaderTail_native`, `Complexity.clHeaderField_native`, `Complexity.clNative_linear`, `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_fields`.
