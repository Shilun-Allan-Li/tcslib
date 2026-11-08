<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Verifier Configuration

**Claim.** For every binary input, the verifier’s initial configuration is in the syntax state with formula-level scanner state, no input bits consumed, empty work tape, work head at zero, and empty output.

**Proof.** Expand the machine’s initial configuration and the stated configuration form. Both have the initial machine state, input-head position one (the shifted representation of zero bits consumed), an everywhere-empty work tape, work-head position zero, and empty output. Equality of these components gives equality of the configurations.
