<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_center -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Return Scan Step

**Claim.** With the base guide tape fixed to the guide of radius $R$, a schedule step from the return-to-center phase enters the counter-test phase and advances the unary-counter head to $u+1$ when $g=0$; otherwise it remains in the return-to-center phase and moves the guide head to $g+1$.

**Proof.** The return-to-center transition tests whether the symbol under the guide head is the origin marker. By `Complexity.macroCfg_guide`, that symbol is the base guide symbol at position $g$, and `Complexity.guideTape_origin` characterizes it as the origin marker exactly when $g=0$. In that case the transition enters the counter-test phase and moves the unary-counter head one position right, leaving the guide head fixed. Otherwise it stays in the return-to-center phase and moves the guide head one position right. In both cases the resulting head positions and state are exactly those in the claimed macro configuration, by `Complexity.macroCfg_apply`.

**Key facts.** `Complexity.macroCfg_guide`, `Complexity.guideTape_origin`, `Complexity.macroCfg_apply`.
