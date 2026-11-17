<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.RoundContract.orbit_start -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial heads in the orbit hull

**Claim.** Each initial work-head position lies between the minimum and maximum of the contract bounds at orbit indices below $n$ together with the head positions at orbit index $n$.

**Proof.** If $n=0$, the index set used in both hulls has only the index zero. At that index the hull definitions select the orbit’s own head positions, and the zero-th orbit configuration is the starting configuration, so each head lies in the resulting interval. If $n>0$, use the orbit-round theorem (`Turing.RoundContract.orbit_round`) for round index zero. Its head-envelope conclusion applies throughout that round, in particular at time zero, when the machine is still at the starting configuration. Thus every initial head position lies in the stated hull.

**Key facts.** `Turing.RoundContract.orbit_round`.
