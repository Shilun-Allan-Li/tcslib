<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDHost.lean :: Turing.guessRun_mapState_mapState -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of state renamings

**Claim.** Renaming the state of a configuration first by $f$ and then by $g$ gives the same configuration as renaming it once by $g\circ f$.

**Proof.** The two successive renamings affect only the state field; the input-head position, work tapes, work-head positions, and output remain those of $c$. For the state field, mapping an optional state first through $f$ and then through $g$ is the same as mapping it through the composite $g\circ f$. Thus all fields agree.
