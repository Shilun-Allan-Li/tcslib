<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_lookup_parts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization Split at a Transition Record

**Claim.** The serialization splits into the header, all state groups preceding $q$, the records preceding the record indexed by $(u,v)$ in $q$'s group, the transition record for $(q,u,v)$, and a remaining Boolean word, with the stated group and prefix lengths.

**Proof.** Let the state list be the finite range of machine states, and let the action list for a state be its nine transition actions, ordered by input and work-tape read. The lookup fact (`timedCut_Actions_lookup`) says each such action list has length nine and that its entry at the record index of $(u,v)$ is the required transition. Split the state list immediately before and at $q$, and split its action list immediately before and at that record index. The finite-range bounds ensure both entries exist. Map the action-list construction over the state split and flatten the resulting lists of records. The preceding state groups then number $q$, each has nine actions, and the preceding records in $q$'s group number the record index. Finally, the serialization-as-header-followed-by-state-records identity (`timedCut_serialization_actions`) turns these splits into the asserted concatenation; the suffix after the selected record is collected as the remaining word.

**Key facts.** `Turing.timedCut_Actions_lookup`, `Turing.timedCut_serialization_actions`.
