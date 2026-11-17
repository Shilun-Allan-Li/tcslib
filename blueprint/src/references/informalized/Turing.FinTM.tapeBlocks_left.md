<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.tapeBlocks_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Left block values

**Claim.** At the position corresponding to a left-block index $i$, the three-block assembly has value $a(i)$.

**Proof.** The position is embedded into the first block of the assembled index range. By the definition of the three-block assembly, indices in that first block are evaluated by the left family, giving $a(i)$.
