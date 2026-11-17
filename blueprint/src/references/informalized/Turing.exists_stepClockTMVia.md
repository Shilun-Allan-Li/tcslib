<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepClock.lean :: Turing.exists_stepClockTMVia -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clocked simulation of a multi-tape machine

**Claim.** For any finite alphabet containing an embedded Boolean alphabet, there is a finite-state simulator with one additional tape that simulates the machine up to the first halt or predicate-satisfying state, or through the represented deadline if no such state occurs. The construction gives distinct terminal state families, the stated time bounds, and the stated intermediate simulation and clock-head invariants.

**Proof.** Choose the simulator furnished by the clocked construction, with control states tagged to distinguish its ordinary run from its terminal controls. Its initial states are the embedded original states; its finish and timeout controls are separate tagged families. The tags make each terminal-state map injective, make the two families disjoint, and keep both disjoint from the initial-state image. For any initial configuration and clock tape satisfying the record hypothesis, the first-stop guarantee supplies the bounded run ending in the finish family, with no earlier entry into either terminal family and with the required intermediate correspondence to original configurations. The timeout guarantee supplies the corresponding endpoint and invariants when no stop occurs by the represented deadline. Combining these two guarantees yields the claimed alternatives and bounds.

**Key facts.** `Turing.sc_finish`, `Turing.sc_timeout`.

**Caveat.** The supplied informal statement is malformed, so the claim and account follow the formal theorem and its proof.
