<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Folding Commutes with an Action

**Claim.** Applying the translated action, with each head's current fold side and folded symbol, to the folded configuration gives exactly the fold of the configuration obtained by applying the original action.

**Proof.** Compare the configuration components. The translated action's successor state records both the original successor state and the new side of every head. The fold-origin identity (`foldCfg_origin`) identifies the origin bit seen by the translated action; the side component of the correctness law for folding a head movement (`foldMove_correct`) then gives the side recorded for the moved head. The input head agrees because folding leaves its position unchanged and the action applies the same input movement on both sides. For each work tape, if the original action does not write, both configurations retain the corresponding tape. If it writes, the tape update agrees by the tape-update compatibility law (`foldTape_update`). The head positions agree by the position component of `foldMove_correct`, using `foldCfg_origin` to supply its origin bit. Finally, the output agrees because the translated action embeds any emitted symbol, and embedding commutes with appending the output symbol to the existing output word.

**Key facts.** `Turing.FinTM.foldCfg_origin`, `Turing.FinTM.foldMove_correct`, `Turing.FinTM.foldTape_update`.
