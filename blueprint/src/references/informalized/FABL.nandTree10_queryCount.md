<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandTree10_queryCount -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query count of the second NAND tree

**Claim.** For every input $x\in\{−1,1\}^2$, the second decision tree makes one query if $x_1=1$ and two queries otherwise.

**Proof.** The second coordinate is either $1$ or $-1$. When it is $1$, the second tree stops after its first query, making one query. When it is $-1$, it queries the other coordinate as well, making two queries. This gives the asserted count in both cases.
