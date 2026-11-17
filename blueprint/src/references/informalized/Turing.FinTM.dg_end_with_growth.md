<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_end_with_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward sweep with leftward growth

**Claim.** When some marked tape head moves left, the backward-writing phase first records which such heads must be marked, then sweeps left to create the new row, and finally writes the boundary marker, reaching the stated left-growth configuration after $k+2$ steps while keeping the head in $[z-k,z]$.

**Proof.** Let $\alpha$ be the transition action and let the new head flags mark exactly those tapes whose old right-head flag is true and whose movement under $\alpha$ is left. The hypothesis `dgCross ... = true` ensures that the simulator takes the branch that stores these flags and enters its indexed sweep phase. The first transition keeps the frontier at $z$ and the head within $[z-k,z]$ (`dgSpan_one`); the fact that the tape is read at the frontier follows from `sweepTape_read`, and the stationary frontier update is captured by `sweepRevCfg_stay`. It then sweeps left across $k$ cells. The left-growth span lemma (`dg_left_span`) places the new row, carrying exactly the stored flags, before the old left stack, removes the corresponding $k$ entries from the right stack, and moves the frontier from $z$ to $z-k$, while keeping the head in that interval. Since the right stack initially consists of the boundary marker and $k>0$, its first $k$ entries are removed. The simulator next writes the boundary marker back at the frontier without moving the head (`dgRev_write_optional`), taking one more step and leaving the left stack and frontier unchanged. Combining these three spans with `dgSpan_add` gives $1+k+1=k+2$ steps and preserves the interval $[z-k,z]$.

**Key facts.** `Turing.FinTM.sweepTape_read`, `Turing.FinTM.sweepRevCfg_stay`, `Turing.FinTM.dgSpan_one`, `Turing.FinTM.dg_left_span`, `Turing.FinTM.dgRev_write_optional`, `Turing.FinTM.dgSpan_add`.
