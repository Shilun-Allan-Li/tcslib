<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.eval_blockMiddleLayer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Middle-layer evaluation

**Claim.** The AND of the middle-layer OR gates equals the parity CNF evaluated on the pattern of block parity signs determined by $x$.

**Proof.** First compare the two sides by the condition that their sign is $-1$. The AND gate outputs $-1$ exactly when every middle input outputs $-1$ (`FABL.CircuitGate.evalFinset_and_eq_neg_one_iff`). Each middle input is the OR gate indexed by a clause, and its value is the clause evaluation on the block-output pattern (`FABL.eval_blockMiddleLayer_get`). The definition of CNF evaluation says its value is $-1$ exactly when every clause evaluates to $-1$; translating between clause indices and list positions gives the same condition for both sides. If this common condition holds, the two signs are both $-1$. If it fails, neither is $-1$, and each must therefore be $1$, since signs have only the values $-1$ and $1$ (`FABL.CNFFormula.sign_eq_of_ne_neg`).

**Key facts.** `FABL.CircuitGate.evalFinset_and_eq_neg_one_iff`, `FABL.eval_blockMiddleLayer_get`, `FABL.CNFFormula.sign_eq_of_ne_neg`.
