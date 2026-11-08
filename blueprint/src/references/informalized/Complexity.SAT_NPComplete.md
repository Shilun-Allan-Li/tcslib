<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.SAT_NPComplete -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# SAT is NP-complete

**Claim.** The language of strings whose decoded CNF formula is satisfiable belongs to NP and is NP-hard.

**Proof.** The result follows by pairing the two established properties: SAT belongs to NP (`SAT_mem_NP`), and SAT is NP-hard (`SAT_NPHard`). These are exactly the membership and hardness conditions in the definition of NP-completeness.

**Key facts.** `Complexity.SAT_mem_NP`, `Complexity.SAT_NPHard`.
