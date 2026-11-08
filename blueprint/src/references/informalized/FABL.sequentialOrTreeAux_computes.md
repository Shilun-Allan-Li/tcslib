<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.sequentialOrTreeAux_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Sequential OR Tree

**Claim.** For any finite set of available coordinates, the sequential OR tree returns $1$ exactly when every available coordinate has value $1$, and otherwise returns $-1$.

**Proof.** Use strong induction on the size of the available set. If the set is empty, the tree returns $1$, and the condition that every available coordinate has value $1$ holds vacuously. Otherwise, the tree queries the least available coordinate $i$. If its value is $-1$, the tree returns $-1$, and the condition that all available coordinates equal $1$ fails at $i$. If its value is not $-1$, then, since the sign alphabet is $\{-1,1\}$, its value is $1$. The tree continues on the set with $i$ removed, where the induction hypothesis says it returns $1$ exactly when all remaining coordinates equal $1$. Together with $x_i=1$, this is precisely the condition that every coordinate in the original set equals $1$.
