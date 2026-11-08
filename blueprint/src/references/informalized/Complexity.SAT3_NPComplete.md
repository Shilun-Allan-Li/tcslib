<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.SAT3_NPComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP-Completeness of Serialized 3-CNF Satisfiability

**Claim.** The language $\mathrm{SAT}_3$ belongs to NP and is NP-hard, hence is NP-complete.

**Proof.** NP-completeness is the conjunction of membership in NP and NP-hardness. The former is supplied by the theorem that $\mathrm{SAT}_3$ belongs to NP (SAT3_mem_NP), and the latter by the theorem that every language in NP reduces to $\mathrm{SAT}_3$ in polynomial time (SAT3_NPHard). Combining these two facts gives the result.

**Key facts.** `Complexity.SAT3_mem_NP`, `Complexity.SAT3_NPHard`.
