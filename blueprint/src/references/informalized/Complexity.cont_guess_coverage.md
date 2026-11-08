<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_guess_coverage -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coverage of Guessed Output Words

**Claim.** If $M$ computes output $v$ from $x$ in $T$ steps, then each length-$T$ choice word produces a guessing-phase configuration with a captured word of length $|v|$, and every such captured word is produced by some length-$T$ choice word.

**Proof.** Form the length-$T$ emission mask, whose entry at each step records whether $M$ emits an output symbol on that step. Its length is $T$ (`cont_mask_length`). The number of true entries equals the number of output symbols produced in those steps: the mask-count identity says that the initial output length plus this number is the final output length (`cont_mask_count`); the initial output is empty, and the computation hypothesis identifies the final output with $v$ (`Turing.FinTM.computesInTime_iff`). For any choice word $w$ of length $T$, the guessing-run formula says the final captured word is the selection of the bits of $w$ at precisely the true positions of the mask (`cont_guess_initial`, `cont_guess_run`). The selected word has length equal to the number of true mask entries (`cont_select_length`), hence length $|v|$. Conversely, every word of that length can be obtained by selecting bits at those positions: the selection map is surjective onto words of the required length (`cont_select_surjective`). Choose a preimage of the desired word and use the same run formula; this gives the required configuration and a choice word of length $T$.

**Key facts.** `Complexity.cont_mask_length`, `Complexity.cont_mask_count`, `Turing.FinTM.computesInTime_iff`, `Complexity.cont_guess_initial`, `Complexity.cont_guess_run`, `Complexity.cont_select_length`, `Complexity.cont_select_surjective`.
