<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingAsymptotics.lean :: FABL.tendsto_exercise9_3_multinomial_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Six-block multinomial ratio limit

**Claim.** For every natural number $d$, the ratio of the six-block multinomial coefficient to $\binom{m+6d}{3d}^2$ tends to $((3d)!)^2/(d!)^6$ as $m$ tends to infinity.

**Proof.** For each $m$, the ratio is exactly $((3d)!)^2/(d!)^6$ multiplied by a fixed-shift factorial ratio (`exercise9_3_ratio_shift_eq`). The fixed-shift factorial ratio tends to $1$ (`tendsto_fixedShiftFactorialRatio`), so the product tends to $((3d)!)^2/(d!)^6$.

**Key facts.** `FABL.exercise9_3_ratio_shift_eq`, `FABL.tendsto_fixedShiftFactorialRatio`.
