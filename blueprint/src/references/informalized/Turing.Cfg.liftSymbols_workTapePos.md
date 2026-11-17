<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftSymbols_workTapePos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Head Positions Under Symbol Lifting

**Claim.** Lifting a Boolean configuration through the embedding preserves the positions of all work tape heads.

**Proof.** The definition of symbol lifting assigns the original work tape head position function unchanged. Therefore the two functions agree at every tape index.
