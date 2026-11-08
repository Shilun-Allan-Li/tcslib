<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Simulation.lean :: Turing.FinTM.tapeBlocks_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right block values

**Claim.** At the position corresponding to a right-block index $i$, the three-block assembly has value $c(i)$.

**Proof.** The position is shifted past the left and buffer blocks into the right block. The definition of the assembly assigns indices in this final block to the right family, so the value there is $c(i)$.
