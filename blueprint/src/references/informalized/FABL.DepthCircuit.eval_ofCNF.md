<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.eval_ofCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Evaluation of a CNF

**Claim.** For every CNF formula and sign vector $x$, the circuit associated with the formula evaluates at $x$ to the same sign as the formula.

**Proof.** First compare the conditions for the two evaluations to equal $-1$. The CNF evaluates to $-1$ exactly when every clause evaluates to $-1$; in the associated circuit, the first-layer gates evaluate as those clauses, and the output OR gate is dual to the first-layer OR gate, hence is AND. Its output is $-1$ exactly when all those clause values are $-1$. Thus the circuit and formula agree on whether their value is $-1$. Since signs have only the two possible values $-1$ and $1$, they must have the same value.
