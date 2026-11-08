<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/MPC/BGW/Privacy.lean :: TCSlib.MPC.BGW.bgwEval_congr_of_isLinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Dependence of Linear Circuit Evaluation

**Claim.** If two input assignments agree at a party $j$ on every input wire, then every linear circuit has the same evaluation at $j$ under both assignments.

**Proof.** Proceed by induction on the circuit. For an input wire, the claim is exactly the assumed agreement of the two assignments at $j$. For a constant circuit, both evaluations are the same constant. If the circuit is an addition gate, linearity means each child is linear; evaluation of the sum is the sum of the child evaluations, and the induction hypotheses identify the two child values at $j$, hence also their sums. If it is multiplication by a public scalar, linearity of the child and the induction hypothesis show that multiplying its equal evaluations by the same scalar preserves equality. A multiplication gate cannot be linear, by the definition of linear circuits, so there is no case to prove there.

**Key facts.** `TCSlib.MPC.BGW.bgwEval_add`, `TCSlib.MPC.BGW.bgwEval_smul`.
