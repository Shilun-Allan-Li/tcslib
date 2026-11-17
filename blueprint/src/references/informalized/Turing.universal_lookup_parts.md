<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universal_lookup_parts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transition Table Decomposition

**Claim.** The serialization decomposes into its header, records for exactly $q$ earlier state groups of nine actions each, records for the actions preceding the read-pair index, the prescribed action's record, and a remaining suffix.

**Proof.** For state $q$, list all nine read-pair actions in their prescribed order. The lookup result for these actions (Turing.universalActions_lookup) says this list has length nine and that the action at the read-pair index is precisely the machine's prescribed transition. Thus the state list can be split into states before $q$, then $q$, then the states after it; likewise its nine-action list can be split at the read-pair index. Take the earlier state groups to be the first split mapped to their action lists, take the preceding actions from the split within the current group, and place the current action's record next. The remaining action records and all later groups form the suffix. The earlier-state list has length $q$, each such group has length nine by the lookup fact, and the preceding-action list has length equal to the read-pair index. The serialization-as-header-followed-by-state-groups identity (Turing.universal_serialization_actions) then gives the asserted concatenation after distributing list mapping and flattening across these splits.

**Key facts.** `Turing.universalActions_lookup`, `Turing.universal_serialization_actions`.
