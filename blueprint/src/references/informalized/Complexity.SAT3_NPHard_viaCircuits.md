<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard.lean :: Complexity.SAT3_NPHard_viaCircuits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-SAT is NP-hard

**Claim.** Every language in NP has a polynomial-time many-one reduction to serialized three-SAT.

**Proof.** Let $L$ be any language in NP. First reduce $L$ to the language of satisfiable encoded Boolean circuits, using the fact that circuit satisfiability is NP-hard (`dagCktSatLang_NPHard`). Then use the polynomial-time reduction from circuit satisfiability to serialized three-SAT (`dagCktSatLang_polyTimeReducible_SAT3`). The composition of polynomial-time many-one reductions is again such a reduction (`PolyTimeReducible.trans`), giving the required reduction from $L$ to three-SAT.

**Key facts.** `BoolCircuit.dagCktSatLang_NPHard`, `BoolCircuit.dagCktSatLang_polyTimeReducible_SAT3`, `Complexity.PolyTimeReducible.trans`.
