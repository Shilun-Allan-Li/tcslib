<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSoundInput.lean :: Complexity.Meyer.input_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the input simulation step

**Claim.** Under the local-check assumptions, if the assignment correctly represents the computation through time $t$ and the time bound holds, then at time $t+1$ it represents the actual input-tape symbol at every offset within the stated input range.

**Proof.** Let $c$ be the actual configuration at time $t$. The induction hypothesis identifies the represented input symbol at time $t$ with the actual symbol at every offset in range. The one-step computation identity expresses the next configuration as one transition from $c$ (`Turing.MultiTapeTM.runFrom_succ_eq_step'`), and the input-tape transition rule describes the resulting symbol at each offset (`Complexity.Meyer.RI_step`). The local input-edge check gives the update relation for offsets inside the input range (`Complexity.Meyer.in_edge`); the boundary check supplies the needed condition at the two extreme offsets (`Complexity.Meyer.bd_edge`).

If $c$ is halted, the input tape stays unchanged, so the input-edge relation and induction hypothesis give the result directly. If $c$ is active and the input head does not move, the same argument applies. For a right move, first consider whether the machine is at a blank boundary cell. The induction hypothesis identifies the represented symbol there with the actual one, so the boundary test agrees in both representations. If the head is clamped at that boundary, the input-edge relation again says the relevant cells stay unchanged, and the induction hypothesis finishes. Otherwise, the input-edge relation shifts the represented symbol from offset $d+1$ to offset $d$; the induction hypothesis identifies that shifted value with the actual symbol after the move. At the far right endpoint, the boundary check instead forces the represented value at the next offset to be blank, matching the actual input’s blank beyond its end.

For a left move, the same reasoning uses the blank-boundary test at the left endpoint. If the head is clamped there, symbols remain unchanged and the induction hypothesis applies. Away from that boundary, the input-edge relation shifts the represented symbol from offset $d-1$ to offset $d$, which the induction hypothesis identifies with the actual symbol. At the far left endpoint, the boundary check ensures the represented value is blank, agreeing with the actual input. These cases establish the claimed equality for every allowed offset.

**Key facts.** `Complexity.Meyer.RI_far`, `Complexity.Meyer.RI_step`, `Complexity.Meyer.bd_edge`, `Complexity.Meyer.in_edge`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
