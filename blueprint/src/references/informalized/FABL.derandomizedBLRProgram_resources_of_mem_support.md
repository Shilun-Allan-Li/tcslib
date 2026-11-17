<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.derandomizedBLRProgram_resources_of_mem_support -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Program resource bounds

**Claim.** Every supported outcome uses zero random examples, exactly three membership queries, and exactly $n+r+(2n+1)+3$ units of local work.

**Proof.** By the supported-outcome cost identity (`derandomizedBLRProgram_cost_eq_of_mem_support`), every outcome has cost `derandomizedBLRCost n r`. Unfolding this cost and the local-work term gives the three components: $0$ random examples, $3$ queries, and $n+r+(2n+1)+3$ units of work.

**Key facts.** `FABL.derandomizedBLRProgram_cost_eq_of_mem_support`.
