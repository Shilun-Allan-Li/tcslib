<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Sizes_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Unary Size Outputs

**Claim.** The maps sending a Boolean word to the unary word of its stored input length and to the unary word of its stored horizon are polynomial-time computable.

**Proof.** First compute the stored header by composing the polynomial-time header-tail and header-field operations (`Complexity.clHeaderTail_native`, `Complexity.clHeaderField_native`, `Complexity.PolyTimeComputable.comp`). From this header, extract the stored input-size field or horizon field, again by the corresponding polynomial-time extraction operation. Finally, fill a word of the extracted length with true bits; this unary-fill operation is polynomial-time computable (`Complexity.clNative_fill`). Closure of polynomial-time computability under composition gives each claimed map.

**Key facts.** `Complexity.clHeaderTail_native`, `Complexity.clHeaderField_native`, `Complexity.PolyTimeComputable.comp`, `Complexity.clNative_fill`.
