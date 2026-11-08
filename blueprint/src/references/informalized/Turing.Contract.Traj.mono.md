<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.Traj.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of trajectory properties

**Claim.** If a contract satisfies a trajectory property $R$, and $R$ implies $R'$ pointwise, then the contract satisfies $R'$.

**Proof.** Fix a datum, an admissible starting configuration, and a time within the contract duration. The trajectory hypothesis gives $R$ for the work-head positions at that time. Apply the pointwise implication from $R$ to $R'$ to obtain the desired property.
