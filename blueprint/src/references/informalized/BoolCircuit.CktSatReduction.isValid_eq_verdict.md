<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid.lean :: BoolCircuit.CktSatReduction.isValid_eq_verdict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity by Circuit Evaluation

**Claim.** For every bit string $w$, its validity indicator equals the disjunction of the verdict on $w$ paired with a string of $|w|$ ones and the verdict on the circuit-kind-swapped string paired with a string of $|w|$ zeros.

**Proof.** Use the characterization of validity by encoded fan-in-two circuits (`isValid_iff`) and the characterization of a verdict on a paired encoding (`verdict_pairEncode`) to turn the equality into equivalence of witnesses. In the forward direction, take a valid circuit $C$ encoded by $w$. Its input count is at most the encoding length (`le_length_encode`), so both chosen strings have enough bits for its inputs. If $C$ evaluates to true on the all-true assignment, it directly witnesses the first verdict. If it evaluates to false there, use the dual circuit. Dualization preserves the fan-in-two condition (`IsFaninTwo.dual`), and its encoding is the swapped encoding (`swapKinds_encode`). The selected all-zero assignment agrees with the negation of the all-true assignment; the dual evaluation identity (`eval_dual`) therefore makes the dual circuit evaluate to true, witnessing the second verdict. In the reverse direction, either verdict supplies an encoded fan-in-two circuit. A witness from the first verdict is already a witness of validity. For a witness from the second, dualize its circuit and use the fact that swapping kinds twice restores the original string (`swapKinds_swapKinds`); the dual circuit then encodes $w$ and establishes validity.

**Key facts.** `BoolCircuit.CktSatReduction.isValid_iff`, `BoolCircuit.CircuitEval.verdict_pairEncode`, `BoolCircuit.CktSatReduction.le_length_encode`, `BoolCircuit.CktSatReduction.IsFaninTwo.dual`, `BoolCircuit.CktSatReduction.swapKinds_encode`, `BoolCircuit.DAGCircuit.eval_dual`, `BoolCircuit.CktSatReduction.swapKinds_swapKinds`.
