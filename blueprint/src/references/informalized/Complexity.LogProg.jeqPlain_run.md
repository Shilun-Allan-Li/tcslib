<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Parse.lean :: Complexity.LogProg.jeqPlain_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Plain Binary Equality Run

**Claim.** The routine skips the unary prefix, compares the plain input word with the register’s binary word, returns to the prescribed initial head positions in the state determined by equality, and stays call-free with the register head in the stated range before its endpoint.

**Proof.** Write the paired input as $2n$ ones followed by the delimiter and $w$. The input-length and indexing calculations establish that the first $2n$ scanned symbols are ones and that the symbols after the delimiter are exactly those of $w$ (`Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.inSym_succ`). The scan lemma moves across the unary prefix while preserving the register head and avoiding call states (`Complexity.LogProg.scanR`). Two further transitions pass the delimiter and enter the comparison state; the input-head movement law identifies their new positions (`Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_pos_val`). The plain comparison routine reads $w$ against the register word and reaches a return state encoding whether the words are equal (`Complexity.LogProg.cmpPlain_run`). The return routine restores both heads and selects the affirmative or negative state accordingly (`Complexity.LogProg.cmpReturn`). Concatenating the scan, transition, comparison, and return stages with the run-addition identity yields the desired total run (`Complexity.LogProg.rrun_add`). The intermediate bounds from the scan, comparison, and return lemmas show that every earlier configuration is call-free and has its register head between $-1$ and the word length.

**Key facts.** `Turing.pairEncode_eq_dbl`, `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.scanR`, `Complexity.LogProg.rrun_one_x`, `Complexity.LogProg.apply_xAct`, `Complexity.LogProg.moveInputPos_pos_val`, `Complexity.LogProg.inSym_succ`, `Complexity.LogProg.cmpPlain_run`, `Complexity.LogProg.cmpReturn`, `Complexity.LogProg.rrun_add`.
