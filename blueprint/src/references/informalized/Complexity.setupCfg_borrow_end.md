<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousSetup.lean :: Complexity.setupCfg_borrow_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Branch at the End of a Borrow Pass

**Claim.** At the end of the borrow pass, one step preserves every tape, head position, and other configuration component, and selects unary-start when the carry is true and budget-start otherwise.

**Proof.** At budget head position $|w|+1$, the captured clock tape has no symbol (`Complexity.clockTape_end`). Thus the transition from borrow phase sees no bit to rewrite and branches solely on the carry: it selects unary-start for true carry and budget-start for false carry, with no writes or head movements. The action-on-setup-configurations rule (`Complexity.setupCfg_apply`) then identifies the resulting configuration componentwise with the one claimed.

**Key facts.** `Complexity.clockTape_end`, `Complexity.setupCfg_apply`.
