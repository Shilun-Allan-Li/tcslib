<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.within -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Contract Endpoint Within a Time Bound

**Claim.** If the contract running time is at most $B$, there is a time no greater than $B$ at which the run reaches the contract endpoint, with no earlier configuration in the exit set.

**Proof.** Choose $t=C.\mathrm{time}(i,d)$. The assumed bound gives $t\le B$. The contract's cut condition excludes the exit set at every earlier time, and its exact-run property identifies the configuration at time $t$ with the contract endpoint. This time therefore has both required properties.
