<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.selectedLayer1DNF_toBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Terms Compute the Next AND Layer

**Claim.** If the first-layer gates are AND gates, the DNF formula made from any selected first-layer terms computes the same Boolean function as the dual next-layer gate applied to those selected outputs.

**Proof.** Fix an input. A DNF evaluates to $-1$ exactly when some term evaluates to $-1$ (`FABL.DNFFormula.eval_eq_neg_one_iff`). Here the selected terms are precisely those indexed by the chosen finite set. Since each first-layer gate is AND, each such term's value equals its first-layer output. The dual of AND is OR, so the next-layer gate on the selected outputs evaluates to $-1$ exactly when at least one selected output is $-1$. The two functions therefore agree on whether their values are $-1$; as both values are signs, they are equal.

**Key facts.** `FABL.DNFFormula.eval_eq_neg_one_iff`.
