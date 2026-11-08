<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.SPACE_subset_RSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Space Is Randomized Space

**Claim.** Every language decidable by a deterministic finite Turing machine within a constant multiple of a space bound is decidable by a randomized finite Turing machine with the same asymptotic space bound.

**Proof.** Take a deterministic machine witnessing membership in the space class, with constant $c$. Regard it as a nondeterministic machine whose two choice transitions both implement the same deterministic transition. Every choice word of length $t$ then produces exactly the deterministic configuration after $t$ steps (`Turing.MultiTapeTM.toNDTM_runWith`), and its space usage is the deterministic space usage at that time (`Turing.MultiTapeTM.toNDTM_spaceUsedWith`). For each input, choose the halting time supplied by the deterministic computation. The deterministic time-space specification gives halting and the output at that time (`Turing.FinTM.computesInTime_iff`); the run correspondence transfers halting to every choice sequence of that length, and the space correspondence gives the same bound. Hence the converted machine uses the required space (`Turing.FinNDTM.usesSpace_of_haltsWithin`). Its output is identical for every choice sequence: it is the membership indicator. If the input belongs to the language, the probability of outputting true is therefore $1$, which is at least $2/3$ (`Turing.FinNDTM.outputProb_eq_one`). If it does not belong, every sequence outputs false. These are exactly the required randomized decision conditions.

**Key facts.** `Turing.MultiTapeTM.toNDTM_runWith`, `Turing.MultiTapeTM.toNDTM_spaceUsedWith`, `Turing.FinTM.computesInTime_iff`, `Turing.FinNDTM.usesSpace_of_haltsWithin`, `Turing.FinNDTM.outputProb_eq_one`.
