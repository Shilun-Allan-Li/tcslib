<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_backward -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Scan Step

**Claim.** With the base guide tape fixed to the guide of radius $R$, a schedule step from the backward phase enters the return-to-center phase and moves the guide head to $g+1$ when $g=-R-1$; otherwise it remains in the backward phase and moves the guide head to $g-1$.

**Proof.** The backward-phase transition tests the symbol under the guide head. By `Complexity.macroCfg_guide`, this is the base guide-tape symbol at position $g$. The characterization of the left edge (`Complexity.guideTape_left`) says that this symbol is the left-edge marker exactly when $g=-R-1$. In that case the transition enters the return-to-center phase and moves the guide head one position right. In every other case it stays in the backward phase and moves the guide head one position left. The resulting configurations follow from the macro-configuration action calculation (`Complexity.macroCfg_apply`), with the integer head-position updates written as $g+1$ and $g-1$.

**Key facts.** `Complexity.macroCfg_guide`, `Complexity.guideTape_left`, `Complexity.macroCfg_apply`.
