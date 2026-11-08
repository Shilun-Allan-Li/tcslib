<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRec_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recorder Invariant Through a Finite Horizon

**Claim.** For every $j\le T$, the recorder reaches, within $j(F(3T+4)+2T+7)$ steps, a configuration encoding the source machine's configuration at time $j$, its movement counts, the accumulated record, and logical time $j$, with a Boolean tag satisfying the boundary condition for the source input-head position.

**Proof.** Proceed by induction on $j$. At time zero, take zero recorder steps and choose the tag to be true. The source machine is in its initial configuration, its counts and record are empty, and the recorder's prepared configuration is exactly the encoding of this data. The initial input-head position satisfies the boundary-tag condition.

For the induction step, suppose the recorder has reached the asserted encoding at time $j<T$. Let $c$ be the source configuration then, and let $n$ be its vector of movement counts. Each count is at most $j$ by the count bound (`clCounts_bound`); hence each count's binary word has length at most $T`, by the binary-width bound (`clElapsed_width`). The row-copying phase therefore appends the row of encoded counts and reaches the clock-test control in at most $F(3T+4)+1$ steps (`clRec_copy`). One clock step advances the logical time from $j$ to $j+1$ (`clRec_tick`). The tracking phase then simulates one source step, updates the counts, and supplies a tag satisfying the next boundary condition, in at most $2T+5$ steps (`clRec_advance`). The updated count vector is indeed the count vector at time $j+1$ (`clCounts_succ`), and the source configuration at that time is its one-step successor (`runFrom_succ_eq_step'`).

Concatenating these phases with the inductive recorder run gives the required configuration at time $j+1`; the run concatenation law and the successor identity (`runFrom_add`, `runFrom_succ_eq_step`) justify this composition. The total added work is bounded by $F(3T+4)+2T+7$. Adding this to the inductive bound $j(F(3T+4)+2T+7)$ gives $(j+1)(F(3T+4)+2T+7)$, completing the induction.

**Key facts.** `Complexity.clCounts_bound`, `Complexity.clElapsed_width`, `Complexity.clRec_copy`, `Complexity.clRec_tick`, `Complexity.clRec_advance`, `Complexity.clCounts_succ`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
