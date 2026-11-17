<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.compLift_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace membership of a lifted query language

**Claim.** Under the stated polynomial output-length bound and logspace decidability assumptions for the indexed output-bit and output-length languages, either lifted query language belongs to logspace.

**Proof.** Choose the query determined by the mode: in length mode it asks whether the queried index is below the output length, and in bit mode it asks whether the indexed output bit is true. The corresponding indexed language is in logspace by the respective assumption in the definition of implicit logspace computability. The language `compLift` is obtained by applying the index-dropping map twice as a preimage to this query language. The map `dropIdx` is itself implicitly logspace computable (`implicitlyLogspaceComputable_dropIdx`), so closure of logspace under preimages of implicitly logspace computable functions (`mem_LOGSPACE_preimage`) preserves membership at each of the two stages.

**Key facts.** `Complexity.implicitlyLogspaceComputable_dropIdx`, `Complexity.mem_LOGSPACE_preimage`.
