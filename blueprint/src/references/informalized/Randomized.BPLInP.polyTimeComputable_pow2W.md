<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.polyTimeComputable_pow2W -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Power-of-Two String Construction

**Claim.** For all natural numbers $B$ and $e$, the function sending a bit string $x$ to $B(|x|+1)^e$ zeros followed by a one is polynomial-time computable.

**Proof.** First, the function that replicates the input length many true bits is polynomial-time computable (\texttt{polyTimeComputable\_polyUnary}). A finite-state transducer can map each such bit to a zero, so applying it to that unary string gives the required number of zeros in polynomial time (\texttt{polyTimeComputable\_transduce} and closure under composition, \texttt{PolyTimeComputable.comp}). Appending the constant string $[\mathrm{true}]$ preserves polynomial-time computability (\texttt{PolyTimeComputable.append} and \texttt{polyTimeComputable\_const}), yielding the stated function.

**Key facts.** `Complexity.polyTimeComputable_polyUnary`, `Complexity.polyTimeComputable_transduce`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_const`, `Complexity.PolyTimeComputable.append`.
