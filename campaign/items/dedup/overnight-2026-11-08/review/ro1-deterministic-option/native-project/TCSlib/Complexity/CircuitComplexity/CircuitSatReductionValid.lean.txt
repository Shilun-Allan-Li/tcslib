/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSatLang

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Recognizing circuit descriptions in polynomial time

The reduction `CKT-SAT ≤p 3SAT` of [AB09, Lem 6.11] must tell descriptions of fan-in-two
circuits (`DAGCircuit.encode`) from other strings before it emits anything.  This file
proves that this test, `BoolCircuit.CktSatReduction.isValid`, is polynomial-time, by
reusing the circuit-value machine of `CircuitEval.lean` twice and De Morgan duality:

* the circuit-value algorithm on `⟨w, 1^|w|⟩` accepts iff `w` describes a fan-in-two
  circuit `C` with `C(1ⁿ) = 1`;
* swapping every `∧` and `∨` label of a description (a one-pass transducer,
  `swapKinds`) turns the description of `C` into that of its *dual* `C^d`, which is
  fan-in two iff `C` is and satisfies `C^d(¬x) = ¬C(x)`; so the algorithm on
  `⟨swapKinds w, 0^|w|⟩` accepts iff `w` describes a fan-in-two circuit with `C(1ⁿ) = 0`.

The disjunction of the two verdicts is therefore exactly validity.  The file also
defines the transducer `descTail` reading off the output vertex of a description.

## Main definitions

* `BoolCircuit.DAGCircuit.dual` — the De Morgan dual of a circuit (labels `∧ ↔ ∨`).
* `BoolCircuit.CktSatReduction.swapKinds` — the label-swapping transducer.
* `BoolCircuit.CktSatReduction.descTail` — the transducer copying the output field.
* `BoolCircuit.CktSatReduction.isValid` — `w` describes a fan-in-two circuit.

## Main results

* `BoolCircuit.DAGCircuit.eval_dual` — `C^d(¬x) = ¬C(x)`.
* `BoolCircuit.CktSatReduction.swapKinds_encode`, `swapKinds_swapKinds` — the
  transducer maps descriptions to descriptions of duals, and is an involution.
* `BoolCircuit.CktSatReduction.isValid_eq_verdict` — validity is the disjunction of two
  circuit-value verdicts.
* `BoolCircuit.CktSatReduction.polyTimeComputable_isValid` — `w ↦ [isValid w]` is in FP.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.1.2, Lemma 6.11; p. 111.)
-/

namespace BoolCircuit

/-! ## De Morgan duals -/

/-- The dual label: `∧ ↔ ∨`, `¬` unchanged. -/
def GateKind.dual : GateKind → GateKind
  | .and => .or
  | .or => .and
  | .not => .not

/-- The dual gate: the same arguments under the dual label. -/
def DAGGate.dual (g : DAGGate) : DAGGate := ⟨g.kind.dual, g.args⟩

private theorem any_eq_not_all {l : List ℕ} {p q : ℕ → Bool} (h : ∀ a ∈ l, p a = !q a) :
    l.any p = !(l.all q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    cases q a <;> simp

private theorem all_eq_not_any {l : List ℕ} {p q : ℕ → Bool} (h : ∀ a ∈ l, p a = !q a) :
    l.all p = !(l.any q) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, List.all_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]
    cases q a <;> simp

/-- On negated values the dual gate computes the negated value of the gate (De Morgan),
provided it reads only existing vertices and, if it is a `¬` gate, reads exactly one
(a `¬` gate of other fan-in negates a conjunction, which has no dual of this form). -/
theorem DAGGate.eval_dual (g : DAGGate) (vals : List Bool)
    (h : ∀ a ∈ g.args, a < vals.length) (hn : g.kind = .not → g.args.length = 1) :
    g.dual.eval (vals.map not) = !(g.eval vals) := by
  have hv : ∀ a ∈ g.args, (vals.map not).getD a false = !(vals.getD a false) := by
    intro a ha
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h a ha)]
  obtain ⟨k, args⟩ := g
  simp only [dual, eval] at hv ⊢
  cases k <;> simp only [GateKind.dual]
  · exact any_eq_not_all hv
  · exact all_eq_not_any hv
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (hn rfl)
    have := h a (by simp)
    simp [List.getElem?_eq_getElem this]

/-- Running dual gates on negated values gives the negated values (gates reading earlier
vertices, `¬` gates of fan-in one). -/
theorem runWith_dual (gs : List DAGGate) (init : List Bool)
    (h : ∀ (i : ℕ) (hi : i < gs.length), ∀ a ∈ (gs[i]).args, a < init.length + i)
    (hn : ∀ g ∈ gs, g.kind = .not → g.args.length = 1) :
    runWith DAGGate.eval (gs.map DAGGate.dual) (init.map not) =
      (runWith DAGGate.eval gs init).map not := by
  induction gs generalizing init with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, runWith_cons]
    rw [DAGGate.eval_dual g init (fun a ha => by simpa using h 0 (by simp) a (by simpa using ha))
      (hn g (by simp))]
    rw [show init.map not ++ [!g.eval init] = (init ++ [g.eval init]).map not by simp]
    apply ih _ _ (fun g hg => hn g (by simp [hg]))
    intro i hi a ha
    have := h (i + 1) (by simpa using hi) a (by simpa using ha)
    simp only [List.length_append, List.length_singleton]
    omega

namespace DAGCircuit

variable {n : ℕ}

/-- **The De Morgan dual** of a circuit: every `∧` becomes `∨` and vice versa; arguments
and output are unchanged. -/
def dual (C : DAGCircuit n) : DAGCircuit n where
  gates := C.gates.map DAGGate.dual
  output := C.output
  args_lt := by
    intro i hi a ha
    simp only [List.getElem_map, DAGGate.dual] at ha
    exact C.args_lt i (by simpa using hi) a ha
  output_lt := by simpa using C.output_lt

/-- **De Morgan for circuits**: the dual of a circuit whose `¬` gates have fan-in one
(e.g. a fan-in-two circuit) outputs, on the negated input, the negated output:
`C^d(¬x) = ¬C(x)`.

**Proof sketch.** By induction along the gate list (`runWith_dual`), the dual's vertex
values on `¬x` are the negations of `C`'s on `x`: each dual gate reads negated values of
existing vertices (`DAGGate.eval_dual`).  The output is an existing vertex. -/
theorem eval_dual (C : DAGCircuit n) (hC : ∀ g ∈ C.gates, g.kind = .not → g.args.length = 1)
    (x : Fin n → Bool) : C.dual.eval (fun i => !x i) = !C.eval x := by
  have hv : C.dual.values (fun i => !x i) = (C.values x).map not := by
    simp only [values, dual]
    rw [show List.ofFn (fun i => !x i) = (List.ofFn x).map not by
      simp [List.map_ofFn, Function.comp_def]]
    exact runWith_dual C.gates (List.ofFn x) (fun i hi a ha => by
      simpa using C.args_lt i hi a ha) hC
  have ho : C.output < (C.values x).length := by simpa using C.output_lt
  simp only [eval, hv]
  rw [show C.dual.output = C.output from rfl]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho]

/-- The dual of a fan-in-two circuit is fan-in two. -/
theorem IsFaninTwo.dual {C : DAGCircuit n} (h : C.IsFaninTwo) : C.dual.IsFaninTwo := by
  obtain ⟨hw, hf⟩ := h
  refine ⟨fun g hg => ?_, fun g hg => ?_⟩
  · simp only [DAGCircuit.dual, List.mem_map] at hg
    obtain ⟨g, hg, rfl⟩ := hg
    obtain ⟨h1, h2⟩ := hw g hg
    refine ⟨h1, fun hk => h2 ?_⟩
    obtain ⟨k, args⟩ := g
    cases k <;> simp_all [DAGGate.dual, GateKind.dual]
  · simp only [DAGCircuit.dual, List.mem_map] at hg
    obtain ⟨g, hg, rfl⟩ := hg
    exact hf g hg

end DAGCircuit

namespace CktSatReduction

open Complexity (transduce polyTimeComputable_transduce)

/-! ## Transducers over circuit descriptions -/

namespace Emitter

/-- The parse states of a circuit description (`DAGCircuit.encode`): reading the number
of inputs (`n`), expecting a gate or the end of the gate list (`g`), the two label bits
(`k1`, `k2`), expecting an argument or the end of the argument list (`a`), inside a unary
argument (`u`), and the output field (`o`). -/
inductive PS
  | n
  | g
  | k1
  | k2 (b : Bool)
  | a
  | u
  | o
  deriving DecidableEq, Fintype

/-- The parse transition. -/
def psNext : PS → Bool → PS
  | .n, true => .n
  | .n, false => .g
  | .g, true => .k1
  | .g, false => .o
  | .k1, b => .k2 b
  | .k2 _, _ => .a
  | .a, true => .u
  | .a, false => .g
  | .u, true => .u
  | .u, false => .a
  | .o, _ => .o

/-- The bit emitted by the label swap: the second label bit after a first bit `0` is
flipped (`00 ↔ 01`, i.e. `∧ ↔ ∨`); every other bit is copied. -/
def swapBit : PS → Bool → Bool
  | .k2 false, b => !b
  | _, b => b

end Emitter

open Emitter

/-- **The label-swapping transducer**: copy the string, flipping the second bit of every
gate label that starts with `0`. -/
def swapKinds (w : List Bool) : List Bool :=
  transduce psNext (fun q b => some (swapBit q b)) .n w

/-- **The output-field transducer**: emit exactly the bits after the end of the gate
list. -/
def descTail (w : List Bool) : List Bool :=
  transduce psNext (fun q b => if q = .o then some b else none) .n w

/-- `T q` is the label swap started in parse state `q`. -/
private def T (q : PS) : List Bool → List Bool :=
  transduce psNext (fun q b => some (swapBit q b)) q

/-- `S q` is the output-field transducer started in parse state `q`. -/
private def S (q : PS) : List Bool → List Bool :=
  transduce psNext (fun q b => if q = .o then some b else none) q

private theorem T_nil (q : PS) : T q [] = [] := rfl

private theorem T_cons (q : PS) (b : Bool) (l : List Bool) :
    T q (b :: l) = swapBit q b :: T (psNext q b) l := rfl

private theorem S_nil (q : PS) : S q [] = [] := rfl

private theorem S_cons (q : PS) (b : Bool) (l : List Bool) :
    S q (b :: l) = (if q = .o then [b] else []) ++ S (psNext q b) l := by
  simp only [S, transduce]
  split_ifs <;> rfl

/-- The swap is an involution from every state: swapping twice gives back the string.

**Proof sketch.** Swapping changes no parse transition (the label state `k2` moves to
`a` whatever the bit), and flipping a bit twice restores it. -/
private theorem T_T (q : PS) (l : List Bool) : T q (T q l) = l := by
  induction l generalizing q with
  | nil => rfl
  | cons b l ih =>
    have hδ : psNext q (swapBit q b) = psNext q b := by
      cases q <;> cases b <;> rfl
    have hb : swapBit q (swapBit q b) = b := by
      cases q <;> try rfl
      rename_i c; cases c <;> simp [swapBit]
    rw [T_cons, T_cons, hδ, hb, ih]

/-- The label swap is an involution. -/
theorem swapKinds_swapKinds (w : List Bool) : swapKinds (swapKinds w) = w := T_T .n w

private theorem T_ones (q : PS) (hq : psNext q true = q) (hs : swapBit q true = true)
    (k : ℕ) (r : List Bool) :
    T q (List.replicate k true ++ r) = List.replicate k true ++ T q r := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, T_cons, hq, hs, ih]

private theorem S_ones (q : PS) (hq : psNext q true = q) (ho : q ≠ .o)
    (k : ℕ) (r : List Bool) :
    S q (List.replicate k true ++ r) = S q r := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, S_cons, hq, ho, ih]

private theorem T_o (r : List Bool) : T .o r = r := by
  induction r with
  | nil => rfl
  | cons b r ih => simp [T_cons, psNext, swapBit, ih]

private theorem S_o (r : List Bool) : S .o r = r := by
  induction r with
  | nil => rfl
  | cons b r ih => simp [S_cons, psNext, ih]

private theorem T_args (args : List ℕ) (r : List Bool) :
    T .a (encodeList encodeNat args ++ r) = encodeList encodeNat args ++ T .g r := by
  induction args with
  | nil => simp [encodeList, T_cons, psNext, swapBit]
  | cons a args ih =>
    simp only [encodeList, encodeNat, List.cons_append, List.append_assoc, T_cons,
      psNext, swapBit]
    rw [T_ones .u rfl rfl]
    simp [T_cons, psNext, swapBit, ih]

private theorem S_args (args : List ℕ) (r : List Bool) :
    S .a (encodeList encodeNat args ++ r) = S .g r := by
  induction args with
  | nil => simp [encodeList, S_cons, psNext]
  | cons a args ih =>
    simp only [encodeList, encodeNat, List.cons_append, List.append_assoc, S_cons,
      psNext, reduceCtorEq, if_false, List.nil_append]
    rw [S_ones .u rfl (by decide)]
    simp [S_cons, psNext, ih]

private theorem T_gates (gs : List DAGGate) (r : List Bool) :
    T .g (encodeList DAGGate.encode gs ++ r) =
      encodeList DAGGate.encode (gs.map DAGGate.dual) ++ r := by
  induction gs with
  | nil => simp [encodeList, T_cons, psNext, swapBit, T_o]
  | cons g gs ih =>
    obtain ⟨k, args⟩ := g
    cases k <;>
      simp [encodeList, DAGGate.encode, GateKind.encode, DAGGate.dual, GateKind.dual,
        T_cons, psNext, swapBit, T_args, ih]

private theorem S_gates (gs : List DAGGate) (r : List Bool) :
    S .g (encodeList DAGGate.encode gs ++ r) = r := by
  induction gs with
  | nil => simp [encodeList, S_cons, psNext, S_o]
  | cons g gs ih =>
    obtain ⟨k, args⟩ := g
    cases k <;>
      simp [encodeList, DAGGate.encode, GateKind.encode, S_cons, psNext, S_args, ih]

/-- **The label swap maps the description of a circuit to that of its dual.** -/
theorem swapKinds_encode {n : ℕ} (C : DAGCircuit n) :
    swapKinds C.encode = C.dual.encode := by
  change T .n _ = _
  simp only [DAGCircuit.encode, encodeNat, List.append_assoc]
  rw [T_ones .n rfl rfl]
  simp [T_cons, psNext, swapBit, T_gates, DAGCircuit.dual]

/-- **The output-field transducer reads off the output vertex** of a description:
`descTail (encode C) = 1^out 0`. -/
theorem descTail_encode {n : ℕ} (C : DAGCircuit n) :
    descTail C.encode = encodeNat C.output := by
  change S .n _ = _
  simp only [DAGCircuit.encode, encodeNat, List.append_assoc]
  rw [S_ones .n rfl (by decide)]
  simp [S_cons, psNext, S_gates]

/-! ## The validity test -/

/-- **Validity of a circuit description**: `w` describes (`DAGCircuit.encode`) a fan-in-two
circuit — exactly the strings the reduction of [AB09, Lem 6.11] maps to a Tseitin formula
(`BoolCircuit.dagCktSatToCNF`). -/
def isValid (w : List Bool) : Bool :=
  match DAGCircuit.decode w with
  | some C => decide C.2.IsFaninTwo
  | none => false

/-- A string is valid iff it is the description of a fan-in-two circuit. -/
theorem isValid_iff (w : List Bool) :
    isValid w = true ↔ ∃ (n : ℕ) (C : DAGCircuit n), C.IsFaninTwo ∧ C.encode = w := by
  constructor
  · intro h
    unfold isValid at h
    cases hd : DAGCircuit.decode w with
    | none => simp [hd] at h
    | some C =>
      rw [hd] at h
      exact ⟨C.1, C.2, of_decide_eq_true h, DAGCircuit.encode_of_decode hd⟩
  · rintro ⟨n, C, hC, rfl⟩
    simp [isValid, DAGCircuit.decode_encode, hC]

/-- The number of inputs of a circuit is at most the length of its description. -/
private theorem le_length_encode {n : ℕ} (C : DAGCircuit n) : n ≤ C.encode.length := by
  simp [DAGCircuit.encode, encodeNat]

/-- **Validity is the disjunction of two circuit values**: `w` describes a fan-in-two
circuit iff the circuit-value algorithm accepts `⟨w, 1^|w|⟩` or `⟨swapKinds w, 0^|w|⟩`.

**Proof sketch.** If `w` describes a fan-in-two circuit `C`, either `C(1ⁿ) = 1` and the
first verdict accepts, or `C(1ⁿ) = 0`; then `swapKinds w` describes the dual
(`swapKinds_encode`), fan-in two, with `C^d(0ⁿ) = ¬C(1ⁿ) = 1` (`eval_dual`).
Conversely an accepting verdict produces a fan-in-two circuit described by `w`, or by
`swapKinds w`; in the latter case `w = swapKinds (swapKinds w)` describes its dual. -/
theorem isValid_eq_verdict (w : List Bool) :
    isValid w = (CircuitEval.verdict false
        (Turing.pairEncode w (List.replicate w.length true)) ||
      CircuitEval.verdict false
        (Turing.pairEncode (swapKinds w) (List.replicate w.length false))) := by
  apply Bool.eq_iff_iff.mpr
  rw [isValid_iff, Bool.or_eq_true, CircuitEval.verdict_pairEncode,
    CircuitEval.verdict_pairEncode]
  constructor
  · rintro ⟨n, C, hC, rfl⟩
    have hn := le_length_encode C
    cases hv : C.eval (fun i => (List.replicate C.encode.length true).getD i false) with
    | true => exact Or.inl ⟨n, C, hC, rfl, by simpa using hn, by simp, hv⟩
    | false =>
      refine Or.inr ⟨n, C.dual, hC.dual, (swapKinds_encode C).symm, by simpa using hn,
        by simp, ?_⟩
      have h1 : (fun i : Fin n => (List.replicate C.encode.length true).getD i false) =
          fun _ => true := by
        funext i
        simp [List.getD_eq_getElem?_getD, show (i : ℕ) <
          C.encode.length by omega]
      have h2 : (fun i : Fin n => (List.replicate C.encode.length false).getD i false) =
          fun i => !((fun _ : Fin n => true) i) := by
        funext i
        simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
        split <;> rfl
      rw [h1] at hv
      rw [h2, DAGCircuit.eval_dual C (fun g hg => (hC.1 g hg).2), hv]
      rfl
  · rintro (⟨n, C, hC, hw, -⟩ | ⟨n, C, hC, hw, -⟩)
    · exact ⟨n, C, hC, hw⟩
    · refine ⟨n, C.dual, hC.dual, ?_⟩
      rw [← swapKinds_encode, hw, swapKinds_swapKinds]

/-- **Validity is decidable in polynomial time**: `w ↦ [isValid w]` is in FP.

**Proof sketch.** Both verdicts of `isValid_eq_verdict` are the accepted circuit-value
machine (`CircuitEval.evalTM_computes`, time `12 (m + 1)²`) after a polynomial-time
pairing (`PolyTimeComputable.pairEncode`) of the identity or the label-swapping
transducer with the transducers `x ↦ 1^|x|`, `x ↦ 0^|x|`.  Concatenating the two
verdict bits and testing for `00` (`Turing.FinTM.computesFunInTime_ifEq`) gives the
disjunction. -/
theorem polyTimeComputable_isValid :
    Complexity.PolyTimeComputable (fun w => [isValid w]) := by
  have hE : Complexity.PolyTimeComputable (fun z => [CircuitEval.verdict false z]) :=
    ⟨CircuitEval.evalTM false, 12, 2, fun z => CircuitEval.evalTM_computes false z⟩
  have hc : ∀ b : Bool, Complexity.PolyTimeComputable
      (fun w : List Bool => List.replicate w.length b) := by
    intro b
    convert polyTimeComputable_transduce (σ := Unit) (fun _ _ => ()) (fun _ _ => some b) ()
      using 1
    funext w
    induction w with
    | nil => rfl
    | cons a w ih => simp [transduce, List.replicate_succ, ih]
  have hS : Complexity.PolyTimeComputable swapKinds := polyTimeComputable_transduce _ _ _
  have h1 := hE.comp (Complexity.polyTimeComputable_id.pairEncode (hc true))
  have h2 := hE.comp (hS.pairEncode (hc false))
  obtain ⟨M, a, hM⟩ := Turing.FinTM.computesFunInTime_ifEq [false, false] [false] [true]
  have hO := Complexity.polyTimeComputable_of_linear ⟨M, a, hM⟩
  convert hO.comp (h1.append h2) using 1
  funext w
  simp only [Function.comp_apply, id, isValid_eq_verdict]
  cases CircuitEval.verdict false (Turing.pairEncode w (List.replicate w.length true)) <;>
    cases CircuitEval.verdict false
      (Turing.pairEncode (swapKinds w) (List.replicate w.length false)) <;> rfl

end CktSatReduction

end BoolCircuit
