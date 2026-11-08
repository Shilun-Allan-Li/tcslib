<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftOver_workTapePos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Head Positions Under Lifting

**Claim.** Lifting a Boolean configuration over a configuration on a same-length input preserves the positions of all work tape heads.

**Proof.** By definition, the work tape head position component of the lifted configuration is exactly the corresponding component of the original Boolean configuration. The claimed equality follows componentwise.
