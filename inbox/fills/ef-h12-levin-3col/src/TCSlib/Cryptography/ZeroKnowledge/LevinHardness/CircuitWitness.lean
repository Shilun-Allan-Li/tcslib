/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Relations
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Bridge
import TCSlib.Complexity.CircuitComplexity.CircuitSatReduction
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.ClassPSPACE.TQBFHard
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The circuit-to-3SAT step of the Levin reduction, with its witness map

Step 2 of the route `(L, R) → (CKT-SAT, R_CKT) → (3SAT, R_3SAT) → (3COL, R_3COL)`: the
instance map is the Tseitin map `BoolCircuit.dagCktSatToSAT3` of [AB09, Lemma 6.11, p. 111]
(polynomial-time by `BoolCircuit.polyTimeComputable_dagCktSatToSAT3`), and the witness map
sends a satisfying input `u` of the circuit described by `d` to the list of the values of all
wires of the circuit on `u`, as [PS10, §4.7, Theorem 124.1, step 2] asks ("Cook's reduction
can be applied to the witness").

The wire values are computed with the circuit-value algorithm `BoolCircuit.CircuitEval.verdict`
(no public all-wire evaluator exists: `CircuitEvalSpec.lean` and `CircuitEvalRun.lean` expose
only the single-output verdict): vertex `v` of `C` is the output of the circuit `C` re-targeted
at `v` (`withOutput`), whose description `retarget C.encode v` is the description of `C` with
its last field `1^out 0` replaced by `1^v 0`. The prefix of the description before that field
is read by a one-pass transducer on the reversed string (`descPrefix`).

## Main definitions

* `TCSlib.Cryptography.LevinHardness.descPrefix` — a description without its output field.
* `TCSlib.Cryptography.LevinHardness.retarget` — a description with output field `1^v 0`.
* `TCSlib.Cryptography.LevinHardness.withOutput` — a circuit re-targeted at vertex `v`.
* `TCSlib.Cryptography.LevinHardness.padInput` — an input padded with `|d|` zeros.
* `TCSlib.Cryptography.LevinHardness.wireValue`, `TCSlib.Cryptography.LevinHardness.wireValues`
  — the value of one wire, and the list of all wire values.

## Main results

* `TCSlib.Cryptography.LevinHardness.wireValues_getD` — on a fan-in-two description the
  computed list is the circuit's vertex values.
* `TCSlib.Cryptography.LevinHardness.polyTimeComputable_wireValues` — the witness map is
  polynomial-time.
* `TCSlib.Cryptography.LevinHardness.R_3SAT_wireValues` — the witness map maps
  `R_CKT` into `R_3SAT` (given the equation of the Tseitin formula, see below).
* `TCSlib.Cryptography.LevinHardness.exists_eval_of_R_3SAT` — a witness of the Tseitin image
  of a fan-in-two circuit gives a satisfying input.

**Disclosures.** The wire-value witness is the design of the EF-H12 brief. The proofs of
`R_3SAT_wireValues` and `exists_eval_of_R_3SAT` follow the pattern of
`BoolCircuit.DAGCircuit.satisfiable_iff_toCNF_satisfiable` (`DAGCircuitSat.lean:354`) and
`Complexity.TQBFHard.toCNF_extension_iff` (`TQBFHardTseitin.lean:67`), with an explicit
witness. `BoolCircuit.DAGCircuit.toCNF` has no published equation; the first theorem
therefore takes it as the hypothesis
`∀ n (C : DAGCircuit n), C.toCNF = [(C.output, true)] :: tseitinGates n C.gates`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§6.1.2, Definition 6.9, Lemma 6.11, p. 111.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7, Theorem 124.1, step 2.)
-/

namespace TCSlib.Cryptography.LevinHardness

open BoolCircuit Std.Sat Complexity Turing

/-! ## The description without its output field -/

/-- The transition of the prefix transducer on the reversed description: state `0` skips
the last bit, state `1` skips the run of `1`s of the output field, state `2` copies. Glue. -/
def stripNext (q : Fin 3) (b : Bool) : Fin 3 :=
  if q = 0 then 1 else if q = 1 ∧ b = true then 1 else 2

/-- Reader of `stripNext`: `stripNext q b = if q = 0 then 1 else if q = 1 ∧ b = true then 1
else 2`. Glue. -/
theorem stripNext_eq (q : Fin 3) (b : Bool) :
    stripNext q b = if q = 0 then 1 else if q = 1 ∧ b = true then 1 else 2 := rfl

/-- The output of the prefix transducer: nothing in states `0` and `1` on a `1`, otherwise the
bit read. Glue. -/
def stripOut (q : Fin 3) (b : Bool) : Option Bool :=
  if q = 0 then none else if q = 1 ∧ b = true then none else some b

/-- Reader of `stripOut`: `stripOut q b = if q = 0 then none else if q = 1 ∧ b = true then
none else some b`. Glue. -/
theorem stripOut_eq (q : Fin 3) (b : Bool) :
    stripOut q b = if q = 0 then none else if q = 1 ∧ b = true then none else some b := rfl

/-- **A description without its output field**: `descPrefix d` is the reverse of the
transducer `transduce stripNext stripOut 0` run on `d.reverse`; on `C.encode` it is
`encodeNat n ++ encodeList DAGGate.encode C.gates` (`descPrefix_encode`). Glue. -/
def descPrefix (d : List Bool) : List Bool :=
  (transduce stripNext stripOut 0 d.reverse).reverse

/-- Reader of `descPrefix`:
`descPrefix d = (transduce stripNext stripOut 0 d.reverse).reverse`. Glue. -/
theorem descPrefix_eq (d : List Bool) :
    descPrefix d = (transduce stripNext stripOut 0 d.reverse).reverse := rfl

/-- A list code ends with its stop bit: `∃ X, encodeList f as = X ++ [false]`. Glue. -/
private theorem encodeList_eq_append_false {α : Type} (f : α → List Bool) (as : List α) :
    ∃ X, encodeList f as = X ++ [false] := by
  induction as with
  | nil => exact ⟨[], by rw [encodeList_nil]; rfl⟩
  | cons a as ih =>
    obtain ⟨X, hX⟩ := ih
    exact ⟨true :: (f a ++ X), by rw [encodeList_cons, hX]; simp⟩

/-- In state `1` the prefix transducer skips a run of `1`s. Glue. -/
private theorem transduce_strip_ones (k : ℕ) (l : List Bool) :
    transduce stripNext stripOut 1 (List.replicate k true ++ l) =
      transduce stripNext stripOut 1 l := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append, transduce_cons, stripNext_eq, stripOut_eq]
    simpa using ih

/-- The prefix of a circuit description: `descPrefix C.encode = encodeNat n ++
encodeList DAGGate.encode C.gates`. Glue.

**Proof sketch.** The gate-list code ends with its stop bit `0`
(`encodeList_eq_append_false`), so the reversed description is
`0 · 1^out · 0 · R` with `R` the rest of the reversed prefix. The transducer drops the first
`0` (state `0`), the run `1^out` (state `1`, `transduce_strip_ones`), emits the next `0` and
copies `R` (state `2`, `Complexity.transduce_of_copy`); reversing gives the prefix. -/
theorem descPrefix_encode {n : ℕ} (C : DAGCircuit n) :
    descPrefix C.encode = encodeNat n ++ encodeList DAGGate.encode C.gates := by
  obtain ⟨X, hX⟩ := encodeList_eq_append_false DAGGate.encode C.gates
  set P := encodeNat n ++ encodeList DAGGate.encode C.gates with hP
  have hrev : P.reverse = false :: (encodeNat n ++ X).reverse := by
    rw [hP, hX, ← List.append_assoc, List.reverse_append]; rfl
  have henc : C.encode = P ++ encodeNat C.output := by
    rw [DAGCircuit.encode_parts, hP, List.append_assoc]
  rw [descPrefix_eq, henc, List.reverse_append, hrev, encodeNat_def, List.reverse_append,
    List.reverse_replicate]
  have hcopy : transduce stripNext stripOut 2 (encodeNat n ++ X).reverse =
      (encodeNat n ++ X).reverse :=
    transduce_of_copy _ _ _ (fun b => by rw [stripNext_eq]; simp)
      (fun b => by rw [stripOut_eq]; simp) _
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rw [transduce_cons, stripNext_eq, stripOut_eq]
  simp only [if_true, Option.toList_none, List.nil_append]
  rw [transduce_strip_ones, transduce_cons, stripNext_eq, stripOut_eq]
  simp only [Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, if_false, Bool.false_eq_true,
    and_false, Option.toList_some, List.singleton_append, hcopy]
  rw [← hrev, List.reverse_reverse]

/-! ## Re-targeting a circuit at a vertex -/

/-- **A description re-targeted at vertex `v`**: `retarget d v = descPrefix d ++ encodeNat v`,
the description `d` with its output field replaced by `1^v 0`. Glue. -/
def retarget (d : List Bool) (v : ℕ) : List Bool := descPrefix d ++ encodeNat v

/-- Reader of `retarget`: `retarget d v = descPrefix d ++ encodeNat v`. Glue. -/
theorem retarget_eq (d : List Bool) (v : ℕ) : retarget d v = descPrefix d ++ encodeNat v := rfl

/-- On a circuit description, `retarget C.encode v = encodeNat n ++
(encodeList DAGGate.encode C.gates ++ encodeNat v)`. Glue. -/
theorem retarget_encode {n : ℕ} (C : DAGCircuit n) (v : ℕ) :
    retarget C.encode v = encodeNat n ++ (encodeList DAGGate.encode C.gates ++ encodeNat v) := by
  rw [retarget_eq, descPrefix_encode, List.append_assoc]

/-- **The circuit `C` with output vertex `v`**, for `v < n + |C.gates|`: the same gates,
`(withOutput C v hv).gates = C.gates` and `(withOutput C v hv).output = v`. Glue. -/
def withOutput {n : ℕ} (C : DAGCircuit n) (v : ℕ) (hv : v < n + C.gates.length) :
    DAGCircuit n :=
  ⟨C.gates, v, C.args_lt, hv⟩

/-- Reader of `withOutput`: its gates are `(withOutput C v hv).gates = C.gates`. Glue. -/
theorem withOutput_gates {n : ℕ} (C : DAGCircuit n) (v : ℕ) (hv : v < n + C.gates.length) :
    (withOutput C v hv).gates = C.gates := rfl

/-- Reader of `withOutput`: its output is `(withOutput C v hv).output = v`. Glue. -/
theorem withOutput_output {n : ℕ} (C : DAGCircuit n) (v : ℕ) (hv : v < n + C.gates.length) :
    (withOutput C v hv).output = v := rfl

/-- The description of the re-targeted circuit is the re-targeted description:
`(withOutput C v hv).encode = retarget C.encode v`. Glue. -/
theorem encode_withOutput {n : ℕ} (C : DAGCircuit n) (v : ℕ) (hv : v < n + C.gates.length) :
    (withOutput C v hv).encode = retarget C.encode v := by
  rw [DAGCircuit.encode_parts, retarget_encode, withOutput_gates, withOutput_output]

/-- Re-targeting keeps fan-in two: `C.IsFaninTwo → (withOutput C v hv).IsFaninTwo`. Glue. -/
theorem isFaninTwo_withOutput {n : ℕ} {C : DAGCircuit n} (hC : C.IsFaninTwo) (v : ℕ)
    (hv : v < n + C.gates.length) : (withOutput C v hv).IsFaninTwo := by
  rw [DAGCircuit.isFaninTwo_iff, withOutput_gates]
  exact (DAGCircuit.isFaninTwo_iff C).mp hC

/-- The re-targeted circuit computes vertex `v`:
`(withOutput C v hv).eval x = (C.values x).getD v false`. Glue. -/
theorem eval_withOutput {n : ℕ} (C : DAGCircuit n) (v : ℕ) (hv : v < n + C.gates.length)
    (x : Fin n → Bool) : (withOutput C v hv).eval x = (C.values x).getD v false := by
  rw [DAGCircuit.eval_eq, DAGCircuit.values_eq, withOutput_gates, withOutput_output,
    ← DAGCircuit.values_eq]

/-- A description of the parts `encodeNat m ++ (encodeList DAGGate.encode G ++ encodeNat o)`
determines them: `n = m`, `C.gates = G` and `C.output = o`. Glue (the parts form of
`BoolCircuit.DAGCircuit.eq_of_encode_eq`, for parts that need not form a circuit). -/
private theorem parts_of_encode_eq {n m : ℕ} {C : DAGCircuit n} {G : List DAGGate} {o : ℕ}
    (h : C.encode = encodeNat m ++ (encodeList DAGGate.encode G ++ encodeNat o)) :
    n = m ∧ C.gates = G ∧ C.output = o := by
  rw [DAGCircuit.encode_parts] at h
  have h1 := congrArg decodeNat h
  rw [decodeNat_encodeNat, decodeNat_encodeNat] at h1
  obtain ⟨hn, hr⟩ := Prod.mk.inj (Option.some.inj h1)
  have hl₁ := length_encodeList_ge DAGGate.encode C.gates
  have hl₂ := length_encodeList_ge DAGGate.encode G
  have hlen := congrArg List.length hr
  simp only [List.length_append] at hlen
  have h2 := congrArg (decodeList DAGGate.decode
    ((encodeList DAGGate.encode G ++ encodeNat o).length + 1)) hr
  rw [decodeList_encodeList DAGGate.decode DAGGate.encode C.gates
      (fun g _ r => DAGGate.decode_encode g r) _ (by simp only [List.length_append]; omega),
    decodeList_encodeList DAGGate.decode DAGGate.encode G
      (fun g _ r => DAGGate.decode_encode g r) _ (by simp only [List.length_append]; omega)]
    at h2
  obtain ⟨hg, ho⟩ := Prod.mk.inj (Option.some.inj h2)
  have ho' := congrArg List.length ho
  simp only [encodeNat_def, List.length_append, List.length_replicate,
    List.length_singleton] at ho'
  exact ⟨hn, hg, by omega⟩

/-! ## The wire values -/

/-- The input padded with `|d|` zeros: `padInput d u = u ++ List.replicate d.length false`
(so that it has at least as many bits as the circuit `d` has inputs). Glue. -/
def padInput (d u : List Bool) : List Bool := u ++ List.replicate d.length false

/-- Reader of `padInput`: `padInput d u = u ++ List.replicate d.length false`. Glue. -/
theorem padInput_eq (d u : List Bool) : padInput d u = u ++ List.replicate d.length false := rfl

/-- Padding does not change the bits read with default `false`:
`(padInput d u).getD i false = u.getD i false`. Glue. -/
theorem padInput_getD (d u : List Bool) (i : ℕ) :
    (padInput d u).getD i false = u.getD i false := by
  rw [padInput_eq]
  by_cases hi : i < u.length
  · exact List.getD_append _ _ _ _ hi
  · rw [List.getD_eq_default u false (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), List.getElem?_replicate]
    split <;> rfl

/-- **The value of wire `v`** of the circuit described by `d` on input `u`: the circuit-value
verdict `CircuitEval.verdict false (pairEncode (retarget d v) (padInput d u))`. Glue. -/
def wireValue (d u : List Bool) (v : ℕ) : Bool :=
  CircuitEval.verdict false (pairEncode (retarget d v) (padInput d u))

/-- Reader of `wireValue`:
`wireValue d u v = CircuitEval.verdict false (pairEncode (retarget d v) (padInput d u))`.
Glue. -/
theorem wireValue_eq (d u : List Bool) (v : ℕ) :
    wireValue d u v = CircuitEval.verdict false (pairEncode (retarget d v) (padInput d u)) :=
  rfl

/-- **The wire-value witness map** ([PS10, §4.7, Theorem 124.1, step 2]): the values of the
vertices `0, …, |d| - 1`, `wireValues d u = (List.range d.length).map (wireValue d u)`. -/
def wireValues (d u : List Bool) : List Bool := (List.range d.length).map (wireValue d u)

/-- Reader of `wireValues`: `wireValues d u = (List.range d.length).map (wireValue d u)`. -/
theorem wireValues_eq (d u : List Bool) :
    wireValues d u = (List.range d.length).map (wireValue d u) := rfl

/-- On a fan-in-two description, wire `v` carries vertex `v`'s value:
`wireValue C.encode u v = (C.values (fun i => u.getD i false)).getD v false`.

**Proof sketch.** By the algorithm's correctness `CircuitEval.verdict_pairEncode`, the verdict
is `true` iff some fan-in-two circuit `C'` on `n' ≤ |padInput|` inputs is described by
`retarget C.encode v` and outputs `1` on the padded input. That description is
`1^n 0 · gates(C) · 1^v 0`, so `C'` has `n` inputs, the gates of `C` and output `v`
(`parts_of_encode_eq`), and its output is vertex `v` of `C` (padding is invisible,
`padInput_getD`). Conversely, if vertex `v` of `C` is `1` then `v` is a vertex
(`length_values`), and `withOutput C v` is such a `C'`
(`encode_withOutput`, `isFaninTwo_withOutput`, `eval_withOutput`); it has
`n ≤ |C.encode| ≤ |padInput|` inputs (`DAGCircuit.size_le_length_encode`). -/
theorem wireValue_encode {n : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo) (u : List Bool)
    (v : ℕ) : wireValue C.encode u v = (C.values (fun i => u.getD i false)).getD v false := by
  have hx : (fun i : Fin n => (padInput C.encode u).getD i false) =
      fun i : Fin n => u.getD i false := funext fun i => padInput_getD _ _ _
  apply Bool.eq_iff_iff.mpr
  rw [wireValue_eq, CircuitEval.verdict_pairEncode]
  constructor
  · rintro ⟨n', C', -, hE, -, -, hev⟩
    rw [retarget_encode] at hE
    obtain ⟨rfl, hg, ho⟩ := parts_of_encode_eq hE
    rw [DAGCircuit.eval_eq, DAGCircuit.values_eq, hg, ho, ← DAGCircuit.values_eq, hx] at hev
    exact hev
  · intro h
    have hv : v < n + C.gates.length := by
      by_contra hv
      rw [List.getD_eq_default _ _ (by rw [DAGCircuit.length_values]; omega)] at h
      exact Bool.false_ne_true h
    have hs := DAGCircuit.size_le_length_encode C
    rw [DAGCircuit.size_eq] at hs
    refine ⟨n, withOutput C v hv, isFaninTwo_withOutput hC v hv, encode_withOutput C v hv,
      ?_, fun h => absurd h Bool.false_ne_true, ?_⟩
    · rw [padInput_eq, List.length_append, List.length_replicate]; omega
    · rw [hx, eval_withOutput]; exact h

/-- **The wire values are the circuit's vertex values** [AB09, Def 6.9]: for a fan-in-two
`C : DAGCircuit n` and every `v`,
`(wireValues C.encode u).getD v false = (C.values (fun i => u.getD i false)).getD v false`.

**Proof sketch.** Below `|C.encode|` this is `wireValue_encode`; from `|C.encode|` on both
sides are `false`, since the description is at least as long as the number of vertices
(`DAGCircuit.size_le_length_encode`, `DAGCircuit.length_values`). -/
theorem wireValues_getD {n : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo) (u : List Bool)
    (v : ℕ) :
    (wireValues C.encode u).getD v false = (C.values (fun i => u.getD i false)).getD v false := by
  rw [wireValues_eq]
  by_cases hv : v < C.encode.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hv]
    exact wireValue_encode C hC u v
  · have hs := DAGCircuit.size_le_length_encode C
    rw [DAGCircuit.size_eq] at hs
    rw [List.getD_eq_default _ _ (by simp only [List.length_map, List.length_range]; omega),
      List.getD_eq_default _ _ (by rw [DAGCircuit.length_values]; omega)]

/-! ## The witness map is polynomial-time -/

/-- `descPrefix` is polynomial-time: a transducer between two reversals. Glue. -/
theorem polyTimeComputable_descPrefix : PolyTimeComputable descPrefix :=
  (BinArith.polyTimeComputable_reverse.comp
      ((polyTimeComputable_transduce stripNext stripOut 0).comp
        BinArith.polyTimeComputable_reverse)).congr fun d => (descPrefix_eq d).symm

/-- **The witness map is polynomial-time**:
`PolyTimeComputable fun z => wireValues (pairFstD z) (pairSndD z)`.

**Proof sketch.** `wireValues d u` concatenates, over `v < |d|`, the one-bit chunks
`[wireValue d u v]` (`List.flatMap` of singletons), so the tabulation host
`ComposeMachines.polyTimeComputable_flatMap_range` applies with the unary count `1^|d|`
(`polyTimeComputable_unary`). The chunk at `⟨1^v, ⟨d, u⟩⟩` is the circuit-value machine
(`CircuitEval.evalTM_computes`, time `12 (m + 1)²`) after pairing
`retarget d v = descPrefix d ++ 1^v 0` (`polyTimeComputable_descPrefix`, the unary map and a
constant) with `padInput d u = u ++ 0^|d|` (`GI.zeros_poly`). -/
theorem polyTimeComputable_wireValues :
    PolyTimeComputable fun z => wireValues (pairFstD z) (pairSndD z) := by
  have hV : PolyTimeComputable fun z => [CircuitEval.verdict false z] :=
    (polyTimeComputable_iff _).mpr ⟨CircuitEval.evalTM false, 12, 2,
      (Turing.FinTM.computesFunInTime_iff _ _ _).mpr fun z => CircuitEval.evalTM_computes false z⟩
  have hD : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hU : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hR : PolyTimeComputable fun w => retarget (pairFstD (pairSndD w)) (pairFstD w).length :=
    ((polyTimeComputable_descPrefix.comp hD).append
      ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).append
        (polyTimeComputable_const [false]))).congr fun w => by
      rw [retarget_eq, encodeNat_def]; rfl
  have hP : PolyTimeComputable fun w => padInput (pairFstD (pairSndD w)) (pairSndD (pairSndD w)) :=
    (hU.append (GI.zeros_poly.comp hD)).congr fun w => by
      rw [padInput_eq]; rfl
  have hE : PolyTimeComputable fun w =>
      [wireValue (pairFstD (pairSndD w)) (pairSndD (pairSndD w)) (pairFstD w).length] :=
    (hV.comp (hR.pairEncode hP)).congr fun _ => rfl
  refine (SecureComputation.ComposeMachines.polyTimeComputable_flatMap_range
    (E := fun z i => [wireValue (pairFstD z) (pairSndD z) i]) hE
    (polyTimeComputable_unary.comp polyTimeComputable_pairFstD)).congr fun z => ?_
  rw [wireValues_eq, List.map_eq_flatMap]

/-! ## The witness relations along the Tseitin map -/

/-- **The witness map maps `R_CKT` into `R_3SAT`** ([AB09, Lemma 6.11, p. 111];
[PS10, §4.7, Theorem 124.1, step 2]):
`R_CKT d u → R_3SAT (dagCktSatToSAT3 d) (wireValues d u)`.

**Proof sketch.** `d = C.encode` for a fan-in-two `C` outputting `1` on `u`. The image is the
serialization of `C.toCNF` (`TQBFHard.dagCktSatToSAT3_encode`), which decodes back
(`CNF.decode_serialize`) to a 3-CNF (`DAGCircuit.toCNF_widthAtMost`). The assignment read from
`wireValues C.encode u` is the vertex-value assignment (`wireValues_getD`), which satisfies the
gate clauses (`DAGCircuit.eval_tseitinGates_values`) and the output clause, the output vertex
being `1` (`DAGCircuit.eval_eq`); the Tseitin formula is read through the quarantined reader
`Bridge.toCNF_eq`. Pattern of `DAGCircuit.satisfiable_iff_toCNF_satisfiable`. -/
theorem R_3SAT_wireValues {d u : List Bool} (h : R_CKT d u) :
    R_3SAT (dagCktSatToSAT3 d) (wireValues d u) := by
  obtain ⟨n, C, hC, rfl, hev⟩ := (R_CKT_iff d u).mp h
  rw [R_3SAT_iff, TQBFHard.dagCktSatToSAT3_encode C hC, CNF.decode_serialize]
  refine ⟨C.toCNF_widthAtMost, ?_⟩
  have hW : (fun v => (wireValues C.encode u).getD v false) =
      fun v => (C.values (fun i => u.getD i false)).getD v false :=
    funext (wireValues_getD C hC u)
  rw [hW, Bridge.toCNF_eq, CNF.eval_cons, C.eval_tseitinGates_values ((DAGCircuit.isFaninTwo_iff C).mp hC).2,
    Bool.and_true, CNF.Clause.eval_cons, CNF.Clause.eval_nil, Bool.or_false, ← DAGCircuit.eval_eq, hev]
  rfl

/-- **The converse along the Tseitin map** [AB09, Lemma 6.11, p. 111]: for a fan-in-two
`C : DAGCircuit n`, `(∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) → ∃ x, C.eval x = true`.

**Proof sketch.** The image decodes to `C.toCNF` (`TQBFHard.dagCktSatToSAT3_encode`,
`CNF.decode_serialize`), so the assignment read from `a` satisfies it; by the pointwise
Tseitin lemma `TQBFHard.toCNF_extension_iff` (taking the assignment itself as the extension)
the circuit outputs `1` on the input it assigns. -/
theorem exists_eval_of_R_3SAT {n : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo)
    (h : ∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) : ∃ x : Fin n → Bool, C.eval x = true := by
  obtain ⟨a, ha⟩ := h
  rw [R_3SAT_iff, TQBFHard.dagCktSatToSAT3_encode C hC, CNF.decode_serialize] at ha
  exact ⟨_, (TQBFHard.toCNF_extension_iff C ((DAGCircuit.isFaninTwo_iff C).mp hC).2
    (fun v => a.getD v false)).mp
    ⟨_, fun _ _ => rfl, ha.2⟩⟩

/-- **The Tseitin map preserves witness existence both ways** ([AB09, Lemma 6.11, p. 111]): for a fan-in-two `C : DAGCircuit n`,
`(∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) ↔ ∃ x : Fin n → Bool, C.eval x = true`.
Glue: `exists_eval_of_R_3SAT`, and `R_3SAT_wireValues` at `u = List.ofFn x`. -/
theorem exists_R_3SAT_iff
    {n : ℕ} (C : DAGCircuit n) (hC : C.IsFaninTwo) :
    (∃ a, R_3SAT (dagCktSatToSAT3 C.encode) a) ↔ ∃ x : Fin n → Bool, C.eval x = true := by
  refine ⟨exists_eval_of_R_3SAT C hC, fun ⟨x, hx⟩ => ⟨_, R_3SAT_wireValues
    ((R_CKT_iff _ (List.ofFn x)).mpr ⟨n, C, hC, rfl, ?_⟩)⟩⟩
  have : (fun i : Fin n => (List.ofFn x).getD i false) = x := funext fun i => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]; simp
  rw [this]; exact hx

end TCSlib.Cryptography.LevinHardness
