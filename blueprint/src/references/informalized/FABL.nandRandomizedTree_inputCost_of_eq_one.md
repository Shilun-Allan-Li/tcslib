<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandRandomizedTree_inputCost_of_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost on the NAND-one input

**Claim.** If the two-input NAND function takes the value $1$ at $x$, the specified randomized decision tree has expected query cost $2$ on $x$.

**Proof.** Since NAND returns $1$ exactly when both coordinates are $-1$, the hypothesis implies $x_0=x_1=-1$. The input-cost formula ( `nandRandomizedTree_inputCost`) expresses the cost as the average of two terms, one for each coordinate: a term is $1$ when that coordinate is $1$, and $2$ otherwise. Both terms are therefore $2$, so their average is $2$.

**Key facts.** `FABL.nandRandomizedTree_inputCost`.
