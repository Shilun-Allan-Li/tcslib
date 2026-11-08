<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clHeaderField_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time computation of header fields

**Claim.** For each fixed natural number $j$, extracting the $j$-th field from a Boolean word encoding a nested-pair header, with empty output when parsing or selection fails, is polynomial-time computable.

**Proof.** The $j$-fold tail extraction is polynomial-time computable (`clHeaderTail_native`). The first component of a decoded pair is also computable in linear time, and hence in polynomial time (`Turing.FinTM.computesFunInTime_pairFst` and `clNative_linear`). Composing these computations preserves polynomial-time computability (`PolyTimeComputable.comp`). Since the desired field is precisely the first component obtained after the tail extraction, this composition computes it.

**Key facts.** `Complexity.clHeaderTail_native`, `Turing.FinTM.computesFunInTime_pairFst`, `Complexity.clNative_linear`, `Complexity.PolyTimeComputable.comp`.
