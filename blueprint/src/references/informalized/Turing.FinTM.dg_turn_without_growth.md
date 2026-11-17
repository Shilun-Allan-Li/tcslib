<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.dg_turn_without_growth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Simulated Turn Without Growth

**Claim.** When no flagged tape moves right, the simulator takes one step from the forward-sweep read configuration to the backward-sweep writing configuration, with the source transition’s updated input position and output. The boundary marker moves to the left stack, the right stack remains $l$, and both endpoint head positions lie in $[z-1,z]$.

**Proof.** Let $d$ be the given read configuration. At frontier $z$, its scanned work symbol is the boundary marker (`sweepTape_read`). The read-boundary rule (`dg_read_boundary`), using input retraction (`dgInput_read`), the agreement of the recorded symbols with the source reads, and the hypothesis that the crossing test is false, identifies the read-state transition with the transition from the completed right-growth state. The turn rule (`dg_turn`) evaluates that transition: it produces the writing state, advances the input head and output according to the source transition, and places the boundary marker on the left while leaving $l$ on the right. The source configuration has the same state, input position, and output as the displayed read configuration, so this resulting configuration is exactly the asserted backward-sweep configuration. The initial head position is $z$ and the final one is $z-1$, hence both lie in $[z-1,z]$; the one-step span lemma (`dgSpan_one`) supplies the claimed span.

**Key facts.** `Turing.FinTM.sweepTape_read`, `Turing.FinTM.dg_read_boundary`, `Turing.FinTM.dgInput_read`, `Turing.FinTM.dg_turn`, `Turing.FinTM.dgSpan_one`.
