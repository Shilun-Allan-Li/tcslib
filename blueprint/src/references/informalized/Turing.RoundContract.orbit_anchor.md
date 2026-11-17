<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.RoundContract.orbit_anchor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Anchor states along the round orbit

**Claim.** If the initial configuration is in the anchor state, the round precondition holds at every orbit index below $n$, and each endpoint with index $r+1<n$ returns to the anchor, then every orbit configuration with index below $n$ is in the anchor state.

**Proof.** Use induction on the orbit index $r$, under the bound $r<n$. At index zero the orbit is the starting configuration, so its state is the anchor by assumption. For the successor index $r+1<n$, the induction hypothesis says that the configuration at index $r$ is in the anchor state, and the precondition holds there. The successor formula for round orbits (`Turing.roundOrbit_succ`) identifies the next orbit configuration with the run from index $r$ for the contract’s duration. The contract run equation identifies this run with the prescribed endpoint. Since $r+1<n$, the return hypothesis says that this endpoint is in the anchor state. This proves the induction step and hence the claim for every $r<n$.

**Key facts.** `Turing.roundOrbit_succ`.
