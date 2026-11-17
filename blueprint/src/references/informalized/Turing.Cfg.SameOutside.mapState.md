<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Cfg.SameOutside.mapState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State mapping preserves tape agreement

**Claim.** Applying a function to the state of one configuration preserves its tape agreement with another configuration outside the same position sets.

**Proof.** Fix a tape and a position outside its designated set. Mapping the state changes only the state component of the configuration; its tape contents are unchanged. Thus the tape value after the mapping is the same as before, and the assumed agreement with the other configuration still holds at this position. This proves agreement outside the sets.
