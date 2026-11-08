<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/SATOracle.lean :: Complexity.coNP_subset_POracle_SAT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoNP Has Polynomial-Time SAT-Oracle Algorithms

**Claim.** Every language whose complement has polynomial-length existential certificates verifiable in polynomial time is decidable in polynomial time with access to a SAT oracle.

**Proof.** Let $L$ be in coNP. Its complement $L^c$ is in NP, so the NP-to-SAT-oracle containment places $L^c$ in polynomial time with a SAT oracle (`Complexity.NP_subset_POracle_SAT`). Polynomial-time oracle computation is closed under complement: a decider can exchange its accepting and rejecting outcomes without changing its time bound (`Complexity.compl_mem_POracle`). Hence $L=(L^c)^c$ also belongs to polynomial time with a SAT oracle.

**Key facts.** `Complexity.NP_subset_POracle_SAT`, `Complexity.compl_mem_POracle`.
