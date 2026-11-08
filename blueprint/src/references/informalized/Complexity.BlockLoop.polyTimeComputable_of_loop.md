<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/PolyTimeBlockLoop.lean :: Complexity.BlockLoop.polyTimeComputable_of_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time for a Bounded Loop

**Claim.** If the state update, emission, and initialization functions are polynomial-time computable, and the iterates have the stated polynomial length bound, then concatenating the emissions from the prescribed number of iterations after initialization is polynomial-time computable.

**Proof.** First consider the function that starts from an arbitrary string $w$, applies $g$ for each index below $a'(|w|+1)^{k'}+1$, and concatenates the corresponding values of $e$. The bounded-iteration emission result (`polyTimeComputable_emitIter`) gives polynomial-time computability of this function from the polynomial-time bounds for $g$ and $e$ and the orbit-length hypothesis. The desired function is exactly this emission function composed with initialization: the assumed identity for each input $z$ identifies their outputs. Since polynomial-time computable functions are closed under composition (`PolyTimeComputable.comp`), the desired function is polynomial-time computable.

**Key facts.** `Complexity.polyTimeComputable_emitIter`, `Complexity.PolyTimeComputable.comp`.
