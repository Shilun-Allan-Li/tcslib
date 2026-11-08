<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.nandRandomizedTree_inputCost_of_eq_neg_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost bound when NAND outputs minus one

**Claim.** Whenever the NAND function on two inputs outputs $-1$, the randomized tree's expected query cost is at most $3/2$.

**Proof.** Use the expected-cost formula for the randomized tree (\texttt{FABL.nandRandomizedTree_inputCost}). Each coordinate is either $1$ or $-1$. If both are $1$, the cost formula gives $(1+1)/2=1$. If exactly one is $-1$, it gives $(1+2)/2=3/2$. The only remaining sign case, both coordinates equal to $-1$, makes NAND output $1$, contrary to the hypothesis. Thus the cost is at most $3/2$.

**Key facts.** `FABL.nandRandomizedTree_inputCost`.
