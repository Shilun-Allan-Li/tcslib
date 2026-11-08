<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_E -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Last Endpoint

**Claim.** For any register state and natural number $k$, replacing the last-endpoint coordinate of its register vector by $k$ gives the register vector of the state with last endpoint set to $k$.

**Proof.** Compare the functions at each register index. At the last-endpoint index $r_E=16$, updating the vector assigns $k$, matching the register vector of the state with $E$ set to $k$. At all other indices, the update preserves the original coordinate, and changing $E$ leaves those coordinates unchanged. Thus the functions agree everywhere.
