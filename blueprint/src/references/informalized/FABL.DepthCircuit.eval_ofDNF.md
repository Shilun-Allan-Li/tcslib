<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.eval_ofDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Circuit Evaluation of a DNF

**Claim.** For every DNF formula and sign vector $x$, the circuit associated with the formula evaluates at $x$ to the same sign as the formula.

**Proof.** The DNF evaluates to $-1$ exactly when some term evaluates to $-1$ (`eval_eq_neg_one_iff`). In the associated circuit, the first-layer gates evaluate as those terms, and the output gate is dual to the first-layer AND gate, hence is OR. The circuit therefore evaluates to $-1$ exactly when at least one term does. The circuit and formula agree on whether the value is $-1$; because each value is either $-1$ or $1$, their values are equal.

**Key facts.** `FABL.DNFFormula.eval_eq_neg_one_iff`.
