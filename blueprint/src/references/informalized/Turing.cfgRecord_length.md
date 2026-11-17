<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.cfgRecord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Configuration Record

**Claim.** The configuration record has exactly $k+3$ fields.

**Proof.** The record consists of the state field, the input-position field, the list of $k$ work-tape fields, and the tag field. Counting these gives $1+1+k+1=k+3$.
