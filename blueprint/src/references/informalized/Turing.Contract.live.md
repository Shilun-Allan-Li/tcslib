<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Nonhalting Before the Exit Time

**Claim.** For a contract entry configuration satisfying the precondition, the machine’s state is not halted at any time strictly before the specified duration.

**Proof.** Fix $u<C.time(i,d)$ and suppose the run is halted at time $u$. The contract endpoint must be nonhalted: its state belongs to the exit set by the endpoint condition, whereas the halted state cannot belong to that set, since the contract’s cut condition excludes the exit set at every earlier time and the endpoint is reached after $u$. More directly, if the endpoint were halted, its membership in the exit set would contradict the cut condition applied at $u$, using the assumed halt at $u$ to identify the endpoint’s state as halted under the run’s persistence after halting. Hence the endpoint state is nonhalted. A run that is nonhalted at a later time is nonhalted at every earlier time (`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`), contradicting the assumed halt at $u$.

**Key facts.** `Turing.MultiTapeTM.runFrom_state_ne_none_of_le`.

**Caveat.** The source establishes endpoint nonhalting by contradiction using the contract exit and cut conditions, but its exact argument relies on the fact that a halted run remains at the same configuration; the proof text obtains this through the run semantics and the rewritten endpoint equality.
