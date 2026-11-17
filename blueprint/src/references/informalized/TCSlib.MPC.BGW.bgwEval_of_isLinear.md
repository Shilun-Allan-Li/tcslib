<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Protocol.lean :: TCSlib.MPC.BGW.bgwEval_of_isLinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Resharer Independence on Linear Circuits

**Claim.** For every input assignment and every linear circuit, its BGW evaluations using resharers $R$ and $R'$ agree as functions on parties.

**Proof.** Proceed by structural induction on the circuit, using its linearity hypothesis. For an input wire or public constant, evaluation does not depend on the resharer, so the evaluations agree directly. For an addition gate, linearity says both subcircuits are linear; evaluation of addition is the sum of the two evaluations (`bgwEval_add`), and the inductive equalities for both children give equality of the sums. For a public-scalar gate, evaluation is scalar multiplication of the child's shares (`bgwEval_smul`), so the inductive equality for the child gives equality at every party. A multiplication gate cannot occur in a linear circuit, since the definition declares such a gate non-linear; thus that case follows from the contradiction with the hypothesis.

**Key facts.** `TCSlib.MPC.BGW.bgwEval_add`, `TCSlib.MPC.BGW.bgwEval_smul`.
