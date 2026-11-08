<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandTree01_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the first NAND tree

**Claim.** The first decision tree computes the function on pairs of signs that returns $1$ exactly when both input coordinates are $-1$, and returns $-1$ otherwise.

**Proof.** Two-input signs can each be either $1$ or $-1$. Split into these two possibilities for the first coordinate and then for the second. In each of the resulting four cases, evaluating the first tree follows its prescribed query branches and returns $1$ precisely in the case where both coordinates are $-1$; in the other three cases it returns $-1$. Thus its value agrees with the NAND function on every input.
