<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.Cfg.embedOracle_state_eq_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Haltedness Under Embedding

**Claim.** The embedded configuration has no current state if and only if the original configuration has no current state.

**Proof.** Embedding sends the optional state through the map that includes each state on the left of the enlarged state type. Mapping an optional value yields none exactly when the original optional value was none: a present state maps to a present included state, while none remains none. Hence the embedded state is none precisely when the original state is none.
