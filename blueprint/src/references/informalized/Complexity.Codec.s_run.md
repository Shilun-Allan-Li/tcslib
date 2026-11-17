<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.s_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired scan execution

**Claim.** Under the stated length, register-bound, endpoint, and oracle-bit hypotheses, the coded simulator executes from the paired scan-test state to the paired scan-finish state. Its accumulated state is the fold of the paired transition rule over the zipped input strings, and only the two scan registers advance by twice their common length.

**Proof.** Apply the general paired scan-loop theorem with the two scan registers as the read positions, the end register as the limit, stride $2$, and the paired transition rule as the state update (`scan_loop`). Its hypotheses about distinct registers and the two advance phases follow from the register assignments and the definitions of the simulator’s scan labels. Each oracle call on a paired input returns the corresponding input bit by the bit-oracle characterization (`orc_bit`); thus the two oracle assumptions supply exactly the bit hypotheses required by the loop theorem. The theorem then gives the stated folded state, advances both scan registers by $2|u|$, leaves the other registers unchanged, and ensures the guard and register bound throughout the finite execution.

**Key facts.** `Complexity.Codec.scan_loop`, `Complexity.Codec.orc_bit`.
