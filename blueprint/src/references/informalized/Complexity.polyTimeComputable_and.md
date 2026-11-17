<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimePairing.lean :: Complexity.polyTimeComputable_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Conjunction

**Claim.** If the one-bit outputs for $p$ and $q$ are polynomial-time computable, then the one-bit output for their conjunction is polynomial-time computable.

**Proof.** Use the polynomial-time conditional construction (`Complexity.polyTimeComputable_ite`) with predicate $p$, true branch the one-bit output for $q$, and false branch the constant word $[\mathrm{false}]$. The predicate is computable by hypothesis, the true branch is computable by the other hypothesis, and the constant branch is polynomial-time computable (`Complexity.polyTimeComputable_const`). The resulting conditional outputs $[q(x)]$ when $p(x)$ is true and $[\mathrm{false}]$ otherwise. A Boolean case split on $p(x)$ identifies this word with $[p(x)\land q(x)]$, giving the desired function.

**Key facts.** `Complexity.polyTimeComputable_ite`, `Complexity.polyTimeComputable_const`.
