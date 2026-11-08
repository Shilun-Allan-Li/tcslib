<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.halted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Halted Configuration

**Claim.** For any register valuation and Boolean answer $b$, the halted configuration is terminating under the guard and accepts exactly when $b$ is true.

**Proof.** The configuration is already halted, so it is terminating by the halted case of the termination definition. The halted-acceptance characterization (\texttt{nacc_halted}) says that acceptance from a halted configuration is equivalent to its stored answer being the Boolean value true. With stored answer $b$, this is exactly the proposition $b=\mathrm{true}$.

**Key facts.** `Complexity.LogProg.nacc_halted`.
