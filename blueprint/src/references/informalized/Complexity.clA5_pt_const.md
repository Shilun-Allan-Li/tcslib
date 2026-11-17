<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5_pt_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Word Computation

**Claim.** For every fixed bit word $w$, the function returning $w$ on every input is polynomial-time computable.

**Proof.** A machine can output the fixed word $w$ on every input within a linear time bound, as supplied by the constant-function computation result (`computesFunInTime_const`). The lemma converting a linear time bound into polynomial-time computability (`clNative_linear`) then gives the claim.

**Key facts.** `Turing.FinTM.computesFunInTime_const`, `Complexity.clNative_linear`.
