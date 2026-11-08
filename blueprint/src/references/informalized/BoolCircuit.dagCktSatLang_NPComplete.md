<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard.lean :: BoolCircuit.dagCktSatLang_NPComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP-completeness of circuit satisfiability

**Claim.** The language of valid encodings of satisfiable Boolean directed acyclic circuits with at most two inputs per gate is NP-complete: it belongs to NP, and every language in NP is polynomial-time many-one reducible to it.

**Proof.** By the NP-membership theorem for this language (`dagCktSatLang_mem_NP`), it belongs to NP. By the NP-hardness theorem (`dagCktSatLang_NPHard`), every language in NP is polynomial-time many-one reducible to it. These are exactly the two clauses in the definition of NP-completeness, so together they establish the result.

**Key facts.** `BoolCircuit.dagCktSatLang_mem_NP`, `BoolCircuit.dagCktSatLang_NPHard`.
