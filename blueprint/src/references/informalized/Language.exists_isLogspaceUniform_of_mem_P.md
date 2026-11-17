<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceTableau.lean :: Language.exists_isLogspaceUniform_of_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logspace-Uniform Circuits for Polynomial Time

**Claim.** Every Boolean-string language decidable in polynomial time has a logspace-uniform family of fan-in-two Boolean circuits of polynomial size that recognizes exactly that language.

**Proof.** By the characterization of polynomial-time languages, choose natural numbers $C,d$ and a machine $M$ deciding the given language within time $C(n+1)^d$ ( `Complexity.mem_P_iff`). Form the circuit family obtained by tabulating this machine's computation. The tabulation theorem gives a logspace-uniform family ( `Complexity.tabFamily_isLogspaceUniform`) and ensures that each circuit has fan-in at most two ( `Complexity.tabFamily_hasFaninTwo`). Logspace uniformity entails polynomial size ( `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize`). Finally, the correctness theorem for the tabulated family identifies its language with the machine's language ( `Complexity.tabFamily_language`), which is the given language by the choice of $M$.

**Key facts.** `Complexity.mem_P_iff`, `Complexity.tabFamily_isLogspaceUniform`, `Complexity.tabFamily_hasFaninTwo`, `BoolCircuit.DAGCircuitFamily.IsLogspaceUniform.isPolySize`, `Complexity.tabFamily_language`.
