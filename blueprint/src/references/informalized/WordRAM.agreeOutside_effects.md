<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.agreeOutside_effects -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement After a Sequence of Effects

**Claim.** If every instruction in a finite list satisfies the condition for writing in $s$, then applying their effects in order leaves the initial memory unchanged at every address outside $s$.

**Proof.** Induct on the instruction list, allowing the starting memory to vary. For the empty list, no effect is applied, so the final memory equals the initial one and agreement follows from reflexivity (\(\texttt{WordRAM.AgreeOutside.refl}\)). For a list beginning with instruction $i$ and followed by a list $l$, the hypothesis gives the write condition for $i$ and for every instruction in $l$. The single-effect result says that the memory after applying $i$ agrees with the starting memory outside $s$ (\(\texttt{WordRAM.agreeOutside_effect}\)). The induction hypothesis says that applying the effects of $l$ to that intermediate memory preserves agreement outside $s$. Transitivity of agreement outside $s$ combines these two conclusions (\(\texttt{WordRAM.AgreeOutside.trans}\)).

**Key facts.** `WordRAM.AgreeOutside.refl`, `WordRAM.agreeOutside_effect`, `WordRAM.AgreeOutside.trans`.
