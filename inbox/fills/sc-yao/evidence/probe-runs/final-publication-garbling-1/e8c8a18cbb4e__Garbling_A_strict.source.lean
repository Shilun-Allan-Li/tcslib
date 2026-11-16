/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.CircuitComplexity.Uniform
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && true) ||
            (false && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

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
  simp only [Function.comp_apply]
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
  simp only [nestedWordEnc_eq, decide_eq_true_eq, Function.comp_apply]

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
Empty conjunction and disjunction are `true` and `false`. [PS10, Protocol 162.6]

**Proof sketch.** Split the argument list into zero, one, two, or at least three entries.
For each gate kind in the first three cases, the public evaluation equations give the
displayed Boolean expression. The fan-in bound excludes the final case. -/
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
    | nil => cases k <;>
          simp [gateOut_eq_eval, DAGGate.eval_eq]
    | cons u args =>
      cases args with
      | nil => cases k <;>
          simp [gateOut_eq_eval, DAGGate.eval_eq, List.range_succ]
      | cons v args =>
        cases args with
        | nil => cases k <;>
          simp [gateOut_eq_eval, DAGGate.eval_eq, List.range_succ]
        | cons w args => simp only [List.length_cons] at hfan; omega


/-- A gate's output assignment bit is polynomial-time when the two kind tests, the
zero and one argument tests, and the first two assignment-bit maps are polynomial-time,
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
  have hAnd : PolyTimeComputable fun z =>
      [if (g z).args.length = 0 then true else if (g z).args.length = 1 then
        (List.ofFn (a z)).getD 0 false
      else (List.ofFn (a z)).getD 0 false && (List.ofFn (a z)).getD 1 false] := by
    convert polyTimeComputable_ite hzero (polyTimeComputable_const [true])
      (polyTimeComputable_ite hone h₀ (polyTimeComputable_and h₀ h₁)) using 1
    funext z
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl
  have hOr : PolyTimeComputable fun z =>
      [if (g z).args.length = 0 then false else if (g z).args.length = 1 then
        (List.ofFn (a z)).getD 0 false
      else (List.ofFn (a z)).getD 0 false || (List.ofFn (a z)).getD 1 false] := by
    convert polyTimeComputable_ite hzero (polyTimeComputable_const [false])
      (polyTimeComputable_ite hone h₀ (polyTimeComputable_or h₀ h₁)) using 1
    funext z
    simp only [decide_eq_true_eq]
    split_ifs <;> rfl
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
    simp [GateKind.encode_and, GateKind.encode_or, GateKind.encode_not]


/-- A selector over at most two argument positions has the corresponding short word list.

**Proof sketch.** Split the argument list into its first three possible lengths and use
the public word-list encoder equations. The position enumeration is a fixed finite list
in each case. -/
private theorem keyList_small (args : List ℕ) (a : Fin args.length → Bool)
    (K : ℕ → Bool → List Bool) (hfan : args.length ≤ 2) :
    BinArith.encWords (List.ofFn fun t => K args[t] (a t)) =
      if args.length = 0 then []
      else if args.length = 1 then
        pairEncode (K (args.getD 0 0) ((List.ofFn a).getD 0 false)) []
      else
        pairEncode (K (args.getD 0 0) ((List.ofFn a).getD 0 false))
          (pairEncode (K (args.getD 1 0) ((List.ofFn a).getD 1 false)) []) := by
  cases args with
  | nil =>
    simp only [List.ofFn_zero, BinArith.encWords_nil]
    rfl
  | cons u args =>
    cases args with
    | nil =>
      simp only [List.ofFn_succ, List.ofFn_zero, BinArith.encWords_cons,
        BinArith.encWords_nil]
      rfl
    | cons v args =>
      cases args with
      | nil =>
        simp only [List.ofFn_succ, List.ofFn_zero, BinArith.encWords_cons,
          BinArith.encWords_nil]
        rfl
      | cons w args => simp only [List.length_cons] at hfan; omega

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
  simpa only [List.map_ofFn] using
    keyList_small (C.gates[i]).args a (fun v b => List.ofFn (keyAt C s v b)) hfan


/-- The encoded argument-key list is polynomial-time if its zero and one argument tests
and the two potential key words are polynomial-time, for fan-in at most two.
[PS10, Protocol 162.6], collecting the keys which encrypt one garbled row. -/
theorem argKeys_poly (inputs width : List Bool → ℕ) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (i : ∀ z, Fin (C z).gates.length)
    (a : ∀ z, Fin ((C z).gates[i z]).args.length → Bool)
    (hfan : ∀ z, ((C z).gates[i z]).args.length ≤ 2)
    (hzero : PolyTimeComputable fun z => [decide (((C z).gates[i z]).args.length = 0)])
    (hone : PolyTimeComputable fun z => [decide (((C z).gates[i z]).args.length = 1)])
    (h₀ : PolyTimeComputable fun z =>
      List.ofFn (keyAt (C z) (s z) (((C z).gates[i z]).args.getD 0 0)
        ((List.ofFn (a z)).getD 0 false)))
    (h₁ : PolyTimeComputable fun z =>
      List.ofFn (keyAt (C z) (s z) (((C z).gates[i z]).args.getD 1 0)
        ((List.ofFn (a z)).getD 1 false))) :
    PolyTimeComputable fun z =>
      BinArith.encWords ((argKeys (C z) (s z) (i z) (a z)).map List.ofFn) := by
  have h := polyTimeComputable_ite hzero (polyTimeComputable_const [])
    (polyTimeComputable_ite hone (h₀.pairEncode (polyTimeComputable_const []))
      (h₀.pairEncode (h₁.pairEncode (polyTimeComputable_const []))))
  refine h.congr fun z => ?_
  simp only [decide_eq_true_eq]
  exact (argKeys_small (C z) (s z) (i z) (a z) (hfan z)).symm


/-- A table with zero, one, or two argument positions is polynomial-time for any constant
assignment enumerations `enum l`, if every corresponding row map is polynomial-time and
the zero and one arity tests are polynomial-time. [PS10, Protocol 162.6]

**Proof sketch.** For each of the three arities, assemble the finite encoded row list with
`fixedTable_poly`. Two polynomial-time tests select its arity. The fan-in bound ensures
that the final branch has arity two, so no algorithm for computing the enumeration is
required, including when the chosen constant lists come from `Finset.univ.toList`. -/
theorem smallArityTable_poly (arity : List Bool → ℕ)
    (enum : ∀ l : ℕ, List (Fin l → Bool))
    (row : ∀ l : ℕ, (Fin l → Bool) → List Bool → List Bool)
    (hbound : ∀ z, arity z ≤ 2)
    (hzero : PolyTimeComputable fun z => [decide (arity z = 0)])
    (hone : PolyTimeComputable fun z => [decide (arity z = 1)])
    (hrow : ∀ l, l ≤ 2 → ∀ a, PolyTimeComputable (row l a)) :
    PolyTimeComputable fun z =>
      BinArith.encWords ((enum (arity z)).map fun a => row (arity z) a z) := by
  have h₀ := fixedTable_poly (enum 0) (row 0) (hrow 0 (by omega))
  have h₁ := fixedTable_poly (enum 1) (row 1) (hrow 1 (by omega))
  have h₂ := fixedTable_poly (enum 2) (row 2) (hrow 2 (by omega))
  have h := polyTimeComputable_ite hzero h₀ (polyTimeComputable_ite hone h₁ h₂)
  refine h.congr fun z => ?_
  simp only [decide_eq_true_eq]
  generalize hk : arity z = k
  have hkbound : k ≤ 2 := by have := hbound z; omega
  have hz : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hz with rfl | rfl | rfl <;> simp

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.Garbling
