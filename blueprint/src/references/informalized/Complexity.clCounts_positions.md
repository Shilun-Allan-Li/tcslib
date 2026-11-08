<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCounts_positions -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Signed Counts Equal Positions

**Claim.** At every time $t$, the signed value of the count pair at coordinate $i$ equals the corresponding reference position in the configuration reached after $t$ steps.

**Proof.** Induct on $t$. At time zero, all counts are zero, and the initial input-head and work-tape positions give the matching signed values directly. For the successor step, the signed count at each coordinate changes by precisely that coordinate’s signed displacement (`Complexity.clSigned_advance`). By induction, the previous signed count is the previous configuration’s position. The machine’s one-step position update adds the same displacement (`Complexity.clMoves_correct`), using the fact that the tag computed from the input-head position correctly records boundary status (`Complexity.clTag_valid`). Finally, the configuration after $t+1$ steps is one machine step after the configuration at time $t$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`), so these updates identify the new signed count with the new position.

**Key facts.** `Complexity.clSigned_advance`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.clMoves_correct`, `Complexity.clTag_valid`.
