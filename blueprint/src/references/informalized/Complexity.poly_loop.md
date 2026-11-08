<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.poly_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness and Cost of a Unary Loop

**Claim.** Under the stated head-position hypotheses, a loop at level $i$ runs for $r(\kappa_{q,C}(i)+2)+q+2$ steps, reaches $\mathrm{advance}_{i+1}$ with the original head positions, and appends $rCq^i$ ones.

**Proof.** The proof first establishes a one-iteration statement for a loop at level $i$. If its marked head is at $j<q$, it reads a $1$ and enters either the emission state (when $i=0$) or the loop at level $i-1$. When $i=0$, the emission chain appends $C$ ones, and the advance transition restores the marked head to its original position. When $i>0$, the induction hypothesis on the smaller level runs the inner loop for its prescribed cost, appends $Cq^{i-1}$ ones, and returns with the lower heads reset. The head-position hypothesis ensures the update at level $i-1$ changes no other head; the identity $q(Cq^{i-1})=Cq^i$ gives the output for this iteration. The recursive definition of $\kappa$ gives the stated iteration cost, including the entry and return steps.

Now induct on the number $r$ of remaining iterations, generalizing the output. If $r=0$, then $j=q$; the loop sees a blank at its marked head, enters rewind, and the rewind result gives the advance state with the head reset and no additional output. If $r+1$ iterations remain, then $j<q$. Apply the one-iteration statement, which advances that head by one and appends $Cq^i$ ones, then apply the induction hypothesis to the remaining $r$ iterations starting at $j+1$. The run-addition law combines their lengths, while concatenation of the two replicated blocks gives $r+1$ copies of the per-iteration output. This yields the claimed total time and output.

**Key facts.** `Complexity.polyMove_apply`, `Complexity.poly_advance`, `Complexity.poly_emit`, `Complexity.poly_rewind`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`.
