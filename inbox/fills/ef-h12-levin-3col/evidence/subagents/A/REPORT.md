# Sub-agent A report (recorded by the lead from A's hand-back message; A's harness refused the file write)

File: TCSlib/Cryptography/ZeroKnowledge/LevinHardness/CircuitWitness.lean (424 lines at hand-back; no sorry/admit/
native_decide/axiom/opaque/@[simp]; width <= 100). Compiled rc 0, no warnings (build.log). A ran a sealed replay
(local irreducible on IsFaninTwo, IsWellFormed, DAGCircuit.encode/values/eval/size, encodeNat, encodeList, decodeNat,
decodeList, DAGGate.decode/encode/eval, runWith, transduce, R_CKT, R_3SAT, dagCktSatToSAT3, CNF.decode/serialize,
DAGCircuit.toCNF, tseitinGates, CircuitEval.verdict/evalTM, pairFstD/SndD, pairEncode, PolyTimeComputable,
CNF.WidthAtMost, FinTM.ComputesFunInTime): rc 0.

Declarations: stripNext/stripOut (transducer, glue), descPrefix (+_encode), retarget (+_encode), withOutput
(+gates/output/encode/isFaninTwo/eval), padInput (+getD), wireValue (+_encode), wireValues (+_getD),
polyTimeComputable_descPrefix, polyTimeComputable_wireValues, R_3SAT_wireValues (hand-back: _of_toCNF_eq with the
Tseitin equation as hypothesis; the lead re-pointed it to Bridge.toCNF_eq after the user's ruling),
exists_eval_of_R_3SAT, exists_R_3SAT_iff. Private glue: encodeList_eq_append_false, transduce_strip_ones,
parts_of_encode_eq.

Deviations: input padded with |d| zeros (verdict_pairEncode needs n <= |x|); descTail has no reader nor poly-time
row, so the output field is stripped by an own transducer on d.reverse; List.map with List.map_eq_flatMap bridge;
verdict machine via polyTimeComputable_iff / computesFunInTime_iff.

MISSING readers: DAGCircuit.toCNF (DAGCircuitSat.lean:267; proposed `toCNF_eq ... := rfl`); CktSatReduction.descTail
(CircuitSatReductionValid.lean:225; worked around).

Near-relatives: satisfiable_iff_toCNF_satisfiable (DAGCircuitSat.lean:354), TQBFHard.toCNF_extension_iff
(TQBFHardTseitin.lean:67) - pattern cited, not restated; parts_of_encode_eq ~ DAGCircuit.eq_of_encode_eq
(Uniform.lean:198) in parts form (needed for out-of-range outputs; Uniform's prefix-freeness lemmas are private);
withOutput has no TCSlib analogue; GI.zeros_poly reused. No public all-wire evaluator exists (CircuitEvalSpec/Run
expose only the single-output verdict).

Foreign readers used: see the lead's reader census in REPORT.md (A's list: verdict_pairEncode CircuitEvalCorrect:607,
evalTM_computes CircuitEvalRun:523, polyTimeComputable_iff ClassNP/PolyTime:79, FinTM.computesFunInTime_iff
Finite:289, encode_parts Uniform:135, encodeList_nil/cons :96/:100, length_encodeList_ge :217,
size_le_length_encode :225, encodeNat_def UnaryCode:49, decodeNat_encodeNat :72, decodeList_encodeList
DAGCircuitSatLang:120, DAGGate.decode_encode :140, isFaninTwo_iff DAGCircuit:531, values_eq :484, eval_eq :492,
length_values :538, size_eq :511, toCNF_widthAtMost DAGCircuitSat:272, eval_tseitinGates_values :312,
TQBFHard.toCNF_extension_iff TQBFHardTseitin:67, TQBFHard.dagCktSatToSAT3_encode TQBFHard:89, CNF.decode_serialize
CNFEncoding:287, transduce_nil/cons/of_copy/polyTimeComputable_transduce Transducer:58/63/83/178,
BinArith.polyTimeComputable_reverse Mul:73, GI.zeros_poly GraphIsomorphism/Efficiency:208,
ComposeMachines.polyTimeComputable_flatMap_range Machines:81, PolyTimeComputable.congr Randomized/Closure:101; Std
CNF.eval_cons, CNF.Clause.eval_cons, CNF.Clause.eval_nil).
