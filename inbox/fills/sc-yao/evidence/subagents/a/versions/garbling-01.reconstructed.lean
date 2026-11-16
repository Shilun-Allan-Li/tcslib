/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.CircuitComplexity.Uniform

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time leaves for circuit garbling

The encryption adapter operates on word lists and arbitrary input words. Its contract
identifies it with the frozen nested-encryption interface on zero, one, or two vector keys.
No circuit-family or seed definition from `Yao.lean` occurs here.

## Main definitions

* `Garbling.nestedWordEnc`: nested special encryption on encoded word lists.

## Main results

* `Garbling.spEncStr_poly`: special encryption of polynomial-time supplied words.
* `Garbling.nestedWordEnc_poly`: the nested adapter is polynomial-time.
* `Garbling.nestedWordEnc_vectors`: the adapter agrees with `nestedSpecial.enc`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Algorithm 157.2 and Protocol 162.6 (nested encryption of garbled rows).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling

open Complexity Turing BoolCircuit

/-- If `E`, `k`, `m`, and `r` are polynomial-time word maps, so is
`z ↦ spEncStr E (k z) (m z) (r z)`. [PS10, Algorithm 157.2] -/
theorem spEncStr_poly {E k m r : List Bool → List Bool} (hE : PolyTimeComputable E)
    (hk : PolyTimeComputable k) (hm : PolyTimeComputable m) (hr : PolyTimeComputable r) :
    PolyTimeComputable fun z => spEncStr E (k z) (m z) (r z) := by
  have h := (polyTimeComputable_spEncFun hE).comp
    (NUPPT.polyTimeComputable_layout (polyTimeComputable_const []) (hk.pairEncode hm)
      (polyTimeComputable_const []) hr)
  convert h using 1
  funext z
  rw [spEncFun_eq, NUPPT.inArg_layout, NUPPT.inCoins_layout, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- On `⟨keys, ⟨m, ⟨r₁, r₂⟩⟩⟩`, return `m` for no key, encrypt under the first key
with `r₁` for one key, or encrypt under the second key with `r₂` and then under the first
with `r₁` for two keys. Longer encoded lists return `[]`. [PS10, Protocol 162.6] -/
def nestedWordEnc (E₁ E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  if pairFstD z = [] then pairFstD (pairSndD z)
  else if pairSndD (pairFstD z) = [] then
    spEncStr E₁ (pairFstD (pairFstD z)) (pairFstD (pairSndD z))
      (pairFstD (pairSndD (pairSndD z)))
  else if pairSndD (pairSndD (pairFstD z)) = [] then
    spEncStr E₂ (pairFstD (pairFstD z))
      (spEncStr E₁ (pairFstD (pairSndD (pairFstD z))) (pairFstD (pairSndD z))
        (pairSndD (pairSndD (pairSndD z)))) (pairFstD (pairSndD (pairSndD z)))
  else []

/-- `nestedWordEnc E₁ E₂ z` branches on zero, one, or two encoded keys and performs
zero, one, or two applications of `spEncStr`, respectively. -/
theorem nestedWordEnc_eq (E₁ E₂ : List Bool → List Bool) (z : List Bool) :
    nestedWordEnc E₁ E₂ z =
      if pairFstD z = [] then pairFstD (pairSndD z)
      else if pairSndD (pairFstD z) = [] then
        spEncStr E₁ (pairFstD (pairFstD z)) (pairFstD (pairSndD z))
          (pairFstD (pairSndD (pairSndD z)))
      else if pairSndD (pairSndD (pairFstD z)) = [] then
        spEncStr E₂ (pairFstD (pairFstD z))
          (spEncStr E₁ (pairFstD (pairSndD (pairFstD z))) (pairFstD (pairSndD z))
            (pairSndD (pairSndD (pairSndD z)))) (pairFstD (pairSndD (pairSndD z)))
      else [] := rfl

/-- If `E₁` and `E₂` are polynomial-time, the total nested adapter is polynomial-time:
`PolyTimeComputable (nestedWordEnc E₁ E₂)`. [PS10, Protocol 162.6]

**Proof sketch.** Read the key list, message, and two nonce words by pair projections.
Special encryption is polynomial-time for any supplied word lengths. The zero-, one-,
and two-key cases are selected by three polynomial-time emptiness tests; malformed input
words are covered by the same total projections and tests. -/
theorem nestedWordEnc_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (nestedWordEnc E₁ E₂) := by
  -- The leaf arguments are total polynomial-time pair projections.
  have hk₁ := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hk₂ := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have hm := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hr₁ := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hr₂ := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  -- Three emptiness tests distinguish the supported encoded list lengths.
  convert polyTimeComputable_ite
    (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD) hm
    (polyTimeComputable_ite
      (polyTimeComputable_isNil.comp
        (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD))
      (spEncStr_poly hE₁ hk₁ hm hr₁)
      (polyTimeComputable_ite
        (polyTimeComputable_isNil.comp (polyTimeComputable_pairSndD.comp
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)))
        (spEncStr_poly hE₂ hk₁ (spEncStr_poly hE₁ hk₂ hm hr₂) hr₁)
        (polyTimeComputable_const []))) using 1
  funext z
  simp only [nestedWordEnc_eq, decide_eq_true_eq]

/-- On at most two vector keys, the word adapter agrees with nested special encryption:
`nestedWordEnc E₁ E₂ ⟨encWords (ks.map ofFn), ⟨ofFn o, ⟨ofFn r.1, ofFn r.2⟩⟩⟩ =
 (nestedSpecial E₁ E₂ n).enc ks o r`. [PS10, Protocol 162.6]

**Proof sketch.** Split by the number of keys. Encoded lists are nested pairs, so the
emptiness tests select their length correctly, even if an individual key is empty.
The public `nestedSpecial_enc` reader then gives exactly the corresponding encryption
expression, including which independent nonce belongs to each encryption layer. -/
theorem nestedWordEnc_vectors {n : ℕ} (E₁ E₂ : List Bool → List Bool)
    (ks : List (Fin n → Bool)) (hks : ks.length ≤ 2) (o : Fin n → Bool)
    (r : (Fin n → Bool) × (Fin n → Bool)) :
    nestedWordEnc E₁ E₂
        (pairEncode (BinArith.encWords (ks.map List.ofFn))
          (pairEncode (List.ofFn o) (pairEncode (List.ofFn r.1) (List.ofFn r.2)))) =
      (nestedSpecial E₁ E₂ n).enc ks o r := by
  -- Pair encodings are nonempty even when a vector has width zero.
  match ks, hks with
  | [], _ =>
    simp only [nestedWordEnc_eq, List.map_nil, BinArith.encWords_nil,
      pairFstD_pairEncode, pairSndD_pairEncode, if_true, nestedSpecial_enc]
  | [k], _ =>
    simp only [nestedWordEnc_eq, List.map_cons, List.map_nil, BinArith.encWords_cons,
      BinArith.encWords_nil, pairFstD_pairEncode, pairSndD_pairEncode,
      pairEncode_ne_nil, if_false, if_true, nestedSpecial_enc]
  | [k₁, k₂], _ =>
    simp only [nestedWordEnc_eq, List.map_cons, List.map_nil, BinArith.encWords_cons,
      BinArith.encWords_nil, pairFstD_pairEncode, pairSndD_pairEncode,
      pairEncode_ne_nil, if_false, if_true, nestedSpecial_enc]
  | _ :: _ :: _ :: _, h =>
    simp only [List.length_cons] at h
    omega


/-- A garbled row is polynomial-time when its encoded argument keys, output key, and both
nonce words are polynomial-time, and its gate has at most two arguments.
[PS10, Protocol 162.6], encryption of one row from supplied seed data. -/
theorem garbledRow_poly {E₁ E₂ : List Bool → List Bool}
    (hE₁ : PolyTimeComputable E₁) (hE₂ : PolyTimeComputable E₂)
    (inputs width : List Bool → ℕ) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : ∀ z, Fin (C z).gates.length)
    (a : ∀ z, Fin ((C z).gates[i z]).args.length → Bool)
    (hfan : ∀ z, ((C z).gates[i z]).args.length ≤ 2)
    (hkeys : PolyTimeComputable fun z =>
      BinArith.encWords ((argKeys (C z) (s z) (i z) (a z)).map List.ofFn))
    (hout : PolyTimeComputable fun z =>
      List.ofFn (keyAt (C z) (s z) (inputs z + i z)
        (gateOut ((C z).gates[i z]) (a z))))
    (hr₁ : PolyTimeComputable fun z => List.ofFn (((s z).2.1 (i z) (a z)).1))
    (hr₂ : PolyTimeComputable fun z => List.ofFn (((s z).2.1 (i z) (a z)).2)) :
    PolyTimeComputable fun z =>
      garbledRow (nestedSpecial E₁ E₂ (width z)) (C z) (s z) (i z) (a z) := by
  have h := (nestedWordEnc_poly hE₁ hE₂).comp
    (hkeys.pairEncode (hout.pairEncode (hr₁.pairEncode hr₂)))
  convert h using 1
  funext z
  rw [garbledRow_eq]
  symm
  apply nestedWordEnc_vectors
  rw [argKeys_eq, List.length_ofFn]
  exact hfan z


/-- Encoding a fixed finite list of polynomial-time word maps is polynomial-time:
`z ↦ encWords (enum.map (fun a => row a z))`. In particular, the enumeration can be any
fixed list of assignments to zero, one, or two argument positions. [PS10, Protocol 162.6] -/
theorem fixedTable_poly {α : Type} (enum : List α) (row : α → List Bool → List Bool)
    (hrow : ∀ a, PolyTimeComputable (row a)) :
    PolyTimeComputable fun z => BinArith.encWords (enum.map fun a => row a z) := by
  induction enum with
  | nil =>
    simpa only [List.map_nil, BinArith.encWords_nil] using polyTimeComputable_const []
  | cons a enum ih =>
    simpa only [List.map_cons, BinArith.encWords_cons] using (hrow a).pairEncode ih


/-- For at most two arguments, `gateOut g a` is the conjunction, disjunction, or negated
conjunction of the first zero, one, or two assignment bits, according to `g.kind`.
Empty conjunction and disjunction are `true` and `false`. [PS10, Protocol 162.6] -/
theorem gateOut_small (g : DAGGate) (a : Fin g.args.length → Bool)
    (hfan : g.args.length ≤ 2) :
    gateOut g a =
      if g.kind = .and then
        if g.args.length = 0 then true else if g.args.length = 1 then
          (List.ofFn a).getD 0 false
        else (List.ofFn a).getD 0 false && (List.ofFn a).getD 1 false
      else if g.kind = .or then
        if g.args.length = 0 then false else if g.args.length = 1 then
          (List.ofFn a).getD 0 false
        else (List.ofFn a).getD 0 false || (List.ofFn a).getD 1 false
      else !(if g.args.length = 0 then true else if g.args.length = 1 then
          (List.ofFn a).getD 0 false
        else (List.ofFn a).getD 0 false && (List.ofFn a).getD 1 false) := by
  cases g with
  | mk k args =>
    cases args with
    | nil => cases k <;> rw [gateOut_eq_eval, DAGGate.eval_eq] <;> rfl
    | cons u args =>
      cases args with
      | nil => cases k <;> rw [gateOut_eq_eval, DAGGate.eval_eq] <;> rfl
      | cons v args =>
        cases args with
        | nil => cases k <;> rw [gateOut_eq_eval, DAGGate.eval_eq] <;> rfl
        | cons w args => simp only [List.length_cons] at hfan; omega


/-- A gate's output assignment bit is polynomial-time when the two kind tests, the
zero-/one-argument tests, and the first two assignment-bit maps are polynomial-time,
provided every gate has at most two arguments. [PS10, Protocol 162.6]

**Proof sketch.** Build the conjunction and disjunction of the at most two supplied bits,
with their empty and one-bit cases. Two kind tests choose conjunction, disjunction, or
negated conjunction. The bounded-arity equation `gateOut_small` identifies this finite
Boolean calculation with the public gate-output interface. -/
theorem gateOut_poly (g : List Bool → DAGGate)
    (a : ∀ z, Fin (g z).args.length → Bool)
    (hfan : ∀ z, (g z).args.length ≤ 2)
    (hkAnd : PolyTimeComputable fun z => [decide ((g z).kind = .and)])
    (hkOr : PolyTimeComputable fun z => [decide ((g z).kind = .or)])
    (hzero : PolyTimeComputable fun z => [decide ((g z).args.length = 0)])
    (hone : PolyTimeComputable fun z => [decide ((g z).args.length = 1)])
    (h₀ : PolyTimeComputable fun z => [(List.ofFn (a z)).getD 0 false])
    (h₁ : PolyTimeComputable fun z => [(List.ofFn (a z)).getD 1 false]) :
    PolyTimeComputable fun z => [gateOut (g z) (a z)] := by
  -- Compute each kind's output from at most two assignment bits.
  have hAnd := polyTimeComputable_ite hzero (polyTimeComputable_const [true])
    (polyTimeComputable_ite hone h₀ (polyTimeComputable_and h₀ h₁))
  have hOr := polyTimeComputable_ite hzero (polyTimeComputable_const [false])
    (polyTimeComputable_ite hone h₀ (polyTimeComputable_or h₀ h₁))
  have h := polyTimeComputable_ite hkAnd hAnd
    (polyTimeComputable_ite hkOr hOr (polyTimeComputable_not hAnd))
  -- The formula uses only the public gate-output equation.
  refine h.congr fun z => ?_
  simp only [decide_eq_true_eq]
  rw [gateOut_small (g z) (a z) (hfan z)]
  split_ifs <;> rfl


/-- A gate-kind equality test is polynomial-time when its kind code is:
`z ↦ [decide (k z = tag)]`. This applies to all three constructor tags. -/
theorem gateKind_test_poly (k : List Bool → GateKind)
    (hcode : PolyTimeComputable fun z => (k z).encode) (tag : GateKind) :
    PolyTimeComputable fun z => [decide (k z = tag)] := by
  have h := polyTimeComputable_pairEq.comp (hcode.pairEncode
    (polyTimeComputable_const tag.encode))
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  cases k z <;> cases tag <;>
    simp only [GateKind.encode_and, GateKind.encode_or, GateKind.encode_not] <;> rfl


/-- For a gate with at most two arguments, its encoded argument keys are the zero-, one-,
or two-entry word list selected by its argument count. The two possible entries read
argument positions zero and one with defaults. [PS10, Protocol 162.6]

**Proof sketch.** Use the published argument-key equation. Split the argument list into
its zero-, one-, and two-element cases; in each, the fixed-length `ofFn` reads precisely
the stated positions. Longer lists contradict the fan-in hypothesis. -/
theorem argKeys_small {m n : ℕ} (C : DAGCircuit m)
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (i : Fin C.gates.length) (a : Fin (C.gates[i]).args.length → Bool)
    (hfan : (C.gates[i]).args.length ≤ 2) :
    BinArith.encWords ((argKeys C s i a).map List.ofFn) =
      if (C.gates[i]).args.length = 0 then []
      else if (C.gates[i]).args.length = 1 then
        pairEncode (List.ofFn (keyAt C s ((C.gates[i]).args.getD 0 0)
          ((List.ofFn a).getD 0 false))) []
      else
        pairEncode (List.ofFn (keyAt C s ((C.gates[i]).args.getD 0 0)
          ((List.ofFn a).getD 0 false)))
          (pairEncode (List.ofFn (keyAt C s ((C.gates[i]).args.getD 1 0)
            ((List.ofFn a).getD 1 false))) []) := by
  rw [argKeys_eq]
  generalize hargs : (C.gates[i]).args = args at a hfan ⊢
  cases args with
  | nil =>
    simp only [List.ofFn_zero, List.map_nil, BinArith.encWords_nil]
    rfl
  | cons u args =>
    cases args with
    | nil =>
      simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
        BinArith.encWords_cons, BinArith.encWords_nil]
      rfl
    | cons v args =>
      cases args with
      | nil =>
        simp only [List.ofFn_succ, List.ofFn_zero, List.map_cons, List.map_nil,
          BinArith.encWords_cons, BinArith.encWords_nil]
        rfl
      | cons w args => simp only [List.length_cons] at hfan; omega

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling
