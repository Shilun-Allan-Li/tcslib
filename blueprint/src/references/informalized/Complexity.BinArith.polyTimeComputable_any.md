<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Basic.lean :: Complexity.BinArith.polyTimeComputable_any -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Nonemptiness Test

**Claim.** The function on bit strings that returns the one-bit word $[1]$ if the input contains at least one $1$, and the one-bit word $[0]$ otherwise, is polynomial-time computable.

**Proof.** Use a finite-state transducer that scans the input and emits a $1$ exactly when it sees a $1$. Its output is empty precisely when the input has no $1$: this equivalence follows by induction on the input list, separating a false head from a true head. The polynomial-time empty-output test applied to this transducer thus computes the bit indicating that the input has no $1$. Negating that bit gives the desired nonemptiness indicator, and polynomial-time computability is preserved by composition (`Complexity.polyTimeComputable_transduce`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_isNil`, and `Complexity.polyTimeComputable_not`).

**Key facts.** `Complexity.polyTimeComputable_transduce`, `Complexity.polyTimeComputable_isNil`, `Complexity.PolyTimeComputable.comp`, `Complexity.polyTimeComputable_not`.
