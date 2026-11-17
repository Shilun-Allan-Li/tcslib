<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_seamed_space -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Bound Across Computation Segments

**Claim.** Under the stated bounded-segment and head-position hypotheses, the total space used from the initial configuration through any time is at most $k(2(H+B)+1)$.

**Proof.** Set the radius to $H+B$. It suffices, by the space-from-radius bound (Turing.FinTM.f2_space_radius), to show that every head position in the run from the initial configuration stays within this radius. First consider times up to `startup`: each head begins at zero, and the head-displacement bound (Turing.FinTM.f2_head_steps) puts it between minus the elapsed time and plus the elapsed time. Since `startup ≤ B`, these positions lie within the desired radius. For later times, write the elapsed time as `startup` plus the remaining time. The run-addition identity (Turing.MultiTapeTM.runFrom_add), together with the initialization equation, reduces the claim to the segmented run starting at $c_0$. The bounded-segment head-position result (Turing.FinTM.f2_segment_heads) places every such head within $[-(H+B),H+B]$. Thus the radius bound applies, giving the stated total space estimate.

**Key facts.** `Turing.FinTM.f2_space_radius`, `Turing.FinTM.f2_head_steps`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_segment_heads`.
