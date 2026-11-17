<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.majorityThreeTreeBySeed_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the seeded majority tree

**Claim.** For each seed among $0,1,2$ and every input of three signs, the seeded tree computes the majority function: it returns the sign of the sum of the three inputs, with a nonnegative sum assigned the value $1$.

**Proof.** There are three possible seeds. For seed $0$, the seeded tree is the tree querying coordinates $0$ and $1$ first; for seed $1$, it is the tree querying $0$ and $2$ first; and for seed $2$, it is the tree querying $1$ and $2$ first. In each case, the corresponding fixed tree computes three-sign majority: it returns the first queried sign when the first two signs agree, and otherwise queries the remaining coordinate and returns that sign. The established correctness results for these three trees (`majorityThreeTree01_computes`, `majorityThreeTree02_computes`, and `majorityThreeTree12_computes`) therefore cover all seed cases.

**Key facts.** `FABL.majorityThreeTree01_computes`, `FABL.majorityThreeTree02_computes`, `FABL.majorityThreeTree12_computes`.
