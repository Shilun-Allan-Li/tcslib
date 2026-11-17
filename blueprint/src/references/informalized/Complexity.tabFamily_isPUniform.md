<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableau.lean :: Complexity.tabFamily_isPUniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time uniformity of the tableau family

**Claim.** For every finite-state Turing machine $M$ with Boolean input and output alphabets and all natural numbers $C,d$, the tableau circuit family with time bound $(C+1)(n+1)^d$ is polynomial-time uniform.

**Proof.** Construct the uniformity algorithm by first mapping an input word $x$ to the formatted pair consisting of $x$, a separator, a unary time bound $(C+1)(|x|+1)^d$, another separator, and the empty fixed prefix. This formatting is polynomial-time computable: the identity map, a constant output, and the polynomial unary bound are polynomial-time computable, and the formatting operation preserves polynomial-time computability under composition (Complexity.polyTimeComputable_id, Complexity.polyTimeComputable_const, Complexity.polyTimeComputable_polyUnary, Complexity.polyTimeComputable_tabInput, Complexity.PolyTimeComputable.comp). Next apply the polynomial-time tableau emitter, which is polynomial-time computable (Complexity.UTab.polyTimeComputable_tabEmit). The emitter's specification says that on this formatted input it outputs the encoding of the tableau circuit with input length $n$, time bound $T$, and empty prefix (Complexity.UTab.tabEmit_eq). Here $T=(C+1)(n+1)^d$ is positive, so the specification applies. Consequently the composite algorithm is polynomial-time computable and outputs the encoding of the $n$th circuit on the unary input of length $n$, as required.

**Key facts.** `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_tabInput`, `Complexity.PolyTimeComputable.comp`, `Complexity.UTab.polyTimeComputable_tabEmit`, `Complexity.UTab.tabEmit_eq`.
