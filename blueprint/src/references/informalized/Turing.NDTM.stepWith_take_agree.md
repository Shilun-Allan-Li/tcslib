<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Nondeterministic.lean :: Turing.NDTM.stepWith_take_agree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement After One Step

**Claim.** If two configurations agree in state, input-head position, work tapes, work-tape head positions, and output, and the first input-head position is at most the truncation length, then stepping them with the same choice preserves agreement in all five components. The first run’s input-head position increases by at most one.

**Proof.** First, the two configurations read the same input symbol: the head positions agree, and the first position is within the retained prefix, so `inputSymbol_take_eq` gives equality of the scanned symbols. Their work-head symbols also agree, since their work tapes and work-head positions agree. If the common state is halting, both runs leave their configurations unchanged, by the fact that a halted configuration is fixed by a step (`stepWith_of_halt`). The desired component equalities then follow from the hypotheses, and the input-position bound is immediate. Otherwise, write the common state as $q$. Both runs apply the same transition action, because the choice, state, scanned input symbol, and scanned work symbols are equal. Applying that common action preserves equality of the resulting states, work tapes, work-head positions, and outputs; the input-head positions agree as well. Finally, the input-head movement bound says that stepping from the first position yields a position at most one greater, and that equal starting positions give equal resulting positions (`moveInputPos_val_take`).

**Key facts.** `Turing.NDTM.inputSymbol_take_eq`, `Turing.NDTM.moveInputPos_val_take`, `Turing.NDTM.stepWith_of_halt`.
