<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5EqNum_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Equality of Binary Values

**Claim.** Given polynomial-time computable bit-string functions $f$ and $g$, it is polynomial-time computable to return true exactly when their little-endian binary values are equal.

**Proof.** First form a four-field input containing $f(x)$ in the first field, $g(x)$ in the third field, and empty strings in the other two fields. The fields can be packed in polynomial time (`clNative_fields`), since the two given functions are polynomial-time computable and the empty fields are constant outputs (`clA5_pt_const`). Apply the fixed comparison machine to this packed input. Its correctness statement (`clA5Compare_compute`) says that it returns true exactly when the sum of the binary values in the first two fields equals the sum in the last two. With the two unused fields empty, this is precisely equality of the values of $f(x)$ and $g(x)$. The comparison machine runs in time bounded by a fixed linear polynomial in its input length, so composing it with the polynomial-time field construction gives a polynomial-time computable output (`clNative_image`).

**Key facts.** `Complexity.clNative_fields`, `Complexity.clA5_pt_const`, `Complexity.clA5Compare_compute`, `Complexity.clNative_image`.
