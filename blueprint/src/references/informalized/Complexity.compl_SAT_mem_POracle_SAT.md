<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/SATOracle.lean :: Complexity.compl_SAT_mem_POracle_SAT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement of SAT in Polynomial Oracle Time

**Claim.** The complement of SAT is decidable in polynomial time by a finite oracle Turing machine with oracle SAT; equivalently, $\textsf{SAT}^{c}\in\mathsf{P}^{\textsf{SAT}}$.

**Proof.** The oracle language itself is decidable in polynomial time with access to that same oracle (oracle_mem_POracle). Polynomial oracle time is closed under complement (compl_mem_POracle). Applying this closure to SAT proves that its complement belongs to $\mathsf{P}^{\textsf{SAT}}$.

**Key facts.** `Complexity.oracle_mem_POracle`, `Complexity.compl_mem_POracle`.
