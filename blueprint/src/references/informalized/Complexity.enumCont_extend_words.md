<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_extend_words -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a Word Assignment by One Tape

**Claim.** For $L>0$, assigning $s$ to tape zero among the first $L$ tapes and $y$ to the additional tape $L$ yields tape zero storing $s$, tape $L$ storing $y$, and blank contents on every intervening tape.

**Proof.** Check the equality at each tape index $i$. If $i=0$, the first $L$ tapes include this index because $L>0$, and `stateWord` assigns it $s$. If $i\ne0$ and $i<L$, `stateWord` assigns the empty word, whose tape is blank. In the remaining case, the bound $i<L+1$ forces $i=L$, so the assignment uses $y$ on the added tape. These cases give the stated layout.
