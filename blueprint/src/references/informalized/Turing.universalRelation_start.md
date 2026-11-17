<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universalRelation_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Startup Reaches a Checkpoint

**Claim.** For every effective coding scheme and bit strings $\alpha$ and $x$, the universal machine reaches a configuration in the checkpoint relation within the startup bound.

**Proof.** The initialization result (\texttt{Turing.universal\_initialized}) supplies a time $t$, auxiliary tape contents and head positions, with $t$ within the startup bound, such that the universal machine's configuration at time $t$ is a right extension of the simulation configuration for the decoded machine's initial configuration. The checkpoint relation additionally requires its table cursor to be no greater than the serialized machine's length. Choose the cursor used in that initialization result, namely $2|\operatorname{bits}(n)|+2+q_0+1$, where $n$ is the decoded machine's number of states and $q_0$ its initial state. The header-length bound (\texttt{Turing.universal\_header\_bound}) says this cursor does not exceed the serialization length. These facts give all the witnesses and conditions required by the checkpoint relation.

**Key facts.** `Turing.universal_initialized`, `Turing.universal_header_bound`.
