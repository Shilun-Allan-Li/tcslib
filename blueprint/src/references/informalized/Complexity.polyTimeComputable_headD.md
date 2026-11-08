<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.polyTimeComputable_headD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time First Bit with Default

**Claim.** The function sending a bit string $w$ to the one-bit word containing its first bit, or $0$ if $w$ is empty, is polynomial-time computable.

**Proof.** First append the fixed word $[0]$ to the input. This is polynomial-time computable by closure of polynomial-time functions under concatenation, using the identity function and the constant-function construction (`PolyTimeComputable.append`, `polyTimeComputable_id`, and `polyTimeComputable_const`). Taking the first bit of this extended word is the same as taking its prefix of length one, including when the original input was empty. Thus the desired function is the composition of the append operation followed by taking a prefix of length one. The latter operation is polynomial-time computable, and polynomial-time computability is closed under composition (`polyTimeComputable_take1`, `PolyTimeComputable.comp`).

**Key facts.** `Complexity.PolyTimeComputable.append`, `Complexity.polyTimeComputable_id`, `Complexity.polyTimeComputable_const`, `Complexity.polyTimeComputable_take1`, `Complexity.PolyTimeComputable.comp`.
