<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProg.lean :: Complexity.CounterProg.apply_ctl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Control-Only Action

**Claim.** Applying a control-only action sets the state to $q$, moves the input head as specified, appends the optional output bit $o$, and leaves all work tapes and work-head positions unchanged.

**Proof.** The state, input position, and output are given directly by the action application rule. At every work-tape index the control-only action prescribes no write and zero head movement. Hence each tape is unchanged, and adding zero leaves each work-head position fixed. The resulting configuration has exactly the stated fields.
