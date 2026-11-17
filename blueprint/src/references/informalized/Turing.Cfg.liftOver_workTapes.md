<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/SymbolLift.lean :: Turing.Cfg.liftOver_workTapes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Contents Under Lifting

**Claim.** At each work tape and integer position, the lifted configuration contains the original configuration's symbol when the Boolean tape symbol matches its decoding; otherwise it contains the image under the embedding of the Boolean tape symbol.

**Proof.** Fix a work tape and a position. The work tape contents of the lifted configuration are defined by a conditional: if the Boolean configuration's symbol equals the decoding of the other configuration's symbol, the value is that other symbol; if not, the value is the Boolean configuration's symbol mapped through the embedding. This is precisely the stated formula, by unfolding the definition of lifting over a configuration.
