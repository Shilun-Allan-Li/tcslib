<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.CircuitGate.evalFinset_or_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# OR Evaluation Criterion

**Claim.** The OR gate evaluates to $-1$ on a selected set exactly when some selected index has assigned value $-1$.

**Proof.** By definition, the OR evaluation is $-1$ precisely when there exists a selected index whose value is $-1$; otherwise its value is $1$. This gives the equivalence.
