<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_body_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Body initialization

**Claim.** If the source machine halts with $w$ consecutive true bits, then the body machine started in its initial configuration reaches the anchor with $w$ false bits on tape zero within the stated bound.

**Proof.** Apply the body-call simulation to the source computation from its initial state, in mode 0, with empty starting word and output $\mathrm{replicate}(w,\mathrm{true})$. The call lemma gives a time $t\le 3T+|x|+3w+8$ at which the body machine holds that output on its buffer tape. The initial pair configuration is precisely the body machine's initial configuration, by the pair-configuration/word identification. Now use the copy-completion result with copying map $b\mapsto\mathrm{false}$: since the empty old word is no longer than the output word, it copies the $w$ bits to the seam as false bits and finishes at the anchor after $2w+2$ additional steps. Concatenating the two runs gives the claimed endpoint. The bounds add to $3T+|x|+3w+10$.

**Key facts.** `Complexity.enumCont_body_call`, `Complexity.enumCont_pair_words`, `Complexity.enumCont_copy_complete`, `Turing.MultiTapeTM.runFrom_add`.
