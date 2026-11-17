<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecObserve_step_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Observation Characterizes Core Equality

**Claim.** For configurations $c,d$ whose work tapes are blank outside radius $s$ and whose heads lie within that window, the observation of the one-step successor of $c$ equals the encoded row of $d$ exactly when that successor and $d$ have equal core data and output summaries.

**Proof.** First suppose the successor’s observation agrees with the encoded row of $d$. The work-head bits in that equality show that each successor head lies in the radius-$s$ window: take the cell indexed by the encoded position of the corresponding head, and the head-bit equality identifies its actual position with that cell. Also, the successor’s work tapes are blank outside the window, by the step-preservation fact that a step from a configuration with blank exterior leaves that exterior blank (`codec_step_blank`). Thus the successor satisfies the window hypotheses. The observation-to-row theorem (`codecObserve_eq`) now identifies its observation with its own encoded row. Combining this with the assumed equality and using injectivity of row-bit encoding (`codecRowBits_injective`) shows that the successor’s encoded row equals $d$’s encoded row. The characterization of row equality by core data and output summaries (`codecRowOf_eq_iff`) yields the desired core-sum equality. Conversely, if the successor and $d$ have equal core data and output summaries, their observations agree by the fact that core-sum equality determines observation (`codecObserve_congr`). Since $d$ satisfies the window hypotheses, its observation equals its encoded row by `codecObserve_eq`; chaining these equalities gives the required observation-to-row equality.

**Key facts.** `Complexity.codecObserve_eq`, `Complexity.codecRowBits_injective`, `Complexity.codecRowOf_eq_iff`, `Complexity.codec_step_blank`, `Complexity.codecObserve_congr`.
