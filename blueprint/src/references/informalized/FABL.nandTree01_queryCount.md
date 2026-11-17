<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandTree01_queryCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count of the first NAND tree

**Claim.** For every input $x\in\{−1,1\}^2$, the first decision tree makes one query if $x_0=1$ and two queries otherwise.

**Proof.** The first coordinate is either $1$ or $-1$. If it is $1$, the first tree stops after its initial query, so its query count is one. If it is $-1$, the tree proceeds to query the second coordinate, making two queries in total. These are exactly the two cases in the stated formula.
