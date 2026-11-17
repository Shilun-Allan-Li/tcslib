<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.SAT3_NPHard -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP-Hardness of Serialized 3-CNF Satisfiability

**Claim.** Every language in NP has a polynomial-time many-one reduction to $\mathrm{SAT}_3$.

**Proof.** SAT is NP-hard, and SAT has a polynomial-time many-one reduction to $\mathrm{SAT}_3$. The transitivity theorem for polynomial-time reductions from an NP-hard language transfers NP-hardness along this reduction (NPHard.polyTimeReducible), yielding the claim.

**Key facts.** `Complexity.SAT_NPHard`, `Complexity.SAT_reducible_SAT3`, `Complexity.NPHard.polyTimeReducible`.
