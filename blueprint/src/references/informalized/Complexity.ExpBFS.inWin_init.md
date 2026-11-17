<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Radius.lean :: Complexity.ExpBFS.inWin_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Configuration Lies in Every Window

**Claim.** For every natural number $s$, the initial configuration has all work-tape heads within the window of radius $s$ and all cells outside it blank.

**Proof.** The initial configuration places every work-tape head at the origin and leaves every work-tape cell blank. The general fact that an initial configuration lies in every window (`Turing.Cfg.inWindow_init`), applied to the machine’s initial state and input $x$, gives the claim.

**Key facts.** `Turing.Cfg.inWindow_init`.
