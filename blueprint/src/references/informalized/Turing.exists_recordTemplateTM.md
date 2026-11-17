<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/RecordTable.lean :: Turing.exists_recordTemplateTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Writing a Record Template

**Claim.** For finite decidable state and tag types, there is a deterministic machine that writes the prescribed joined record template in linear time while keeping all work-tape heads within a linear distance of their starting positions.

**Proof.** The visible proof begins by obtaining the bounded-field template machine from `rt_exists_boundFieldTM`, then installs its finite state and decidable equality structure. The `proof_source` supplied for this request ends immediately after beginning the next state-type construction, so it does not reveal the remaining machine composition, case analysis, endpoint argument, or bounds. Consequently the complete proof route cannot be reconstructed faithfully from the provided source.

**Key facts.** `Turing.rt_exists_boundFieldTM`.

**Caveat.** The supplied proof source is truncated after the initial setup; the proof's remaining steps are unavailable.
