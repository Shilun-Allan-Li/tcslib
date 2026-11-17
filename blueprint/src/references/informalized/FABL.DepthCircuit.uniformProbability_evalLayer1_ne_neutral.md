<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.DepthCircuit.uniformProbability_evalLayer1_ne_neutral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-layer gate output probability

**Claim.** For every depth circuit and every gate in its first layer, the uniform probability that the gate's output differs from the neutral value of the dual gate is $2^{-w}$, where $w$ is the width of that gate's term.

**Proof.** Separate the two possible labels of the first-layer gate. If it is AND, its dual is OR, whose neutral value is $1$. The event that the term's output differs from $1$ is precisely the event that the term evaluates to $-1$, which has probability $2^{-w}$ (`FABL.uniformProbability_DNFTerm_eval_neg_one`). If the first-layer gate is OR, its dual is AND, whose neutral value is $-1$. The event that the clause output differs from $-1$ is precisely the event that it equals $1$, which has probability $2^{-w}$ (`FABL.DepthCircuit.uniformProbability_clauseEval_one`). In both cases, the gate duality and neutral-value identities identify the relevant event (`FABL.CircuitGate.dual_and`, `FABL.CircuitGate.neutral_or`, `FABL.CircuitGate.dual_or`, `FABL.CircuitGate.neutral_and`).

**Key facts.** `FABL.CircuitGate.dual_and`, `FABL.CircuitGate.neutral_or`, `FABL.uniformProbability_DNFTerm_eval_neg_one`, `FABL.CircuitGate.dual_or`, `FABL.CircuitGate.neutral_and`, `FABL.DepthCircuit.uniformProbability_clauseEval_one`.
