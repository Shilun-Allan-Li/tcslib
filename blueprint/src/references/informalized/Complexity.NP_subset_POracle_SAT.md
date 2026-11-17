<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassOracle/SATOracle.lean :: Complexity.NP_subset_POracle_SAT -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# NP Is Decidable with a SAT Oracle

**Claim.** Every language in NP belongs to $\mathrm{P}^{\mathrm{SAT}}$, the class decidable in polynomial time with an oracle for SAT.

**Proof.** For any language $L\in\mathrm{NP}$, the NP-hardness of SAT gives a polynomial-time many-one reduction from $L$ to SAT (`SAT_NPHard`). Every language polynomial-time reducible to an oracle language belongs to the corresponding polynomial-time oracle class (`mem_POracle_of_polyTimeReducible`). Applying this fact with oracle SAT gives $L\in\mathrm{P}^{\mathrm{SAT}}$.

**Key facts.** `Complexity.SAT_NPHard`, `Complexity.mem_POracle_of_polyTimeReducible`.
