<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidthScan_serialize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width Scan on Serialized Formulas

**Claim.** For every CNF formula $\varphi$, its width scan after serialization is true exactly when every clause has at most three literal occurrences.

**Proof.** The formula-fold identity (`Complexity.satWidth_formula`) says that scanning the serialization of $\varphi$ from the initial syntax state, zero counter, and true flag ends with flag $\mathrm{true}\wedge W(\varphi)$, where $W(\varphi)$ is the clausewise width test. The scan is defined to return this final flag, so its value is $W(\varphi)$.

**Key facts.** `Complexity.satWidth_formula`.
