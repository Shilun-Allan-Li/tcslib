<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.segment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Contract Run Forms a Segment

**Claim.** For an admissible start in the entry state, the run reaches the prescribed endpoint at the contract time, avoids the exit set at every earlier time, and keeps every work-tape head position within its prescribed interval through that endpoint.

**Proof.** The segment assertion consists of three clauses. The contract’s run property gives the endpoint at time $C.\mathrm{time}(i,d)$; its cut property gives avoidance of the exit set at every earlier time; and its envelope property places each head position in the specified interval at every time up to and including the endpoint. Combining these clauses gives the segment.
