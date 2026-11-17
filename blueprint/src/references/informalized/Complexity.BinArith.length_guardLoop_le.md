<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Iterate.lean :: Complexity.BinArith.length_guardLoop_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Length Bound for a Guarded Update

**Claim.** Under the four stated slot-length bounds, one guarded update produces a bit string of length at most $7L+6$.

**Proof.** The four slot bounds are preserved by the guarded update (`Complexity.BinArith.slotsLe_guardLoop`). The update has two possible forms: it returns the fixed encoding of two empty words, or it returns the nested encoding displayed in the second alternative of `Complexity.BinArith.guardLoop_cases`. In the first case, the fixed pair encoding has length $2+2=4$, which is at most $7L+6$. In the second case, the preserved slot bounds bound the lengths of the decoded components appearing in that nested encoding. Pair encoding contributes twice the length of its first component, an additional two delimiter bits, and the length of its second component (`Turing.length_pairEncode`). The guarded choice in `guardNxt` uses either the output of $g$ when it is no longer than the relevant first component, or that second component itself; in either case its length is bounded by the slot estimate. Substitution of these bounds into the nested pair lengths gives at most $7L+6$. The identities for decoding a pair encoding (`Complexity.pairFstD_pairEncode` and `Complexity.pairSndD_pairEncode`) identify the slots in the output with the corresponding encoded components.

**Key facts.** `Complexity.BinArith.slotsLe_guardLoop`, `Complexity.BinArith.guardLoop_cases`, `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Turing.length_pairEncode`.

**Caveat.** The proof source relies on the algebraic slot substitutions and final integer inequalities without spelling them out; the supplied `SlotsLe` hypotheses and the two guard branches determine the estimates, but their full expansion is omitted.
