/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GarblingProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.WordLists
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
            (true && coe && projection)
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
# Polynomial-time Alice messages from generic circuit and seed readers

The interface assembles the actual encoded garbled tables, the selected input keys, and
the output decoding pairs. Circuit families, raw selectors, description maps, and seed block
equations are parameters. No definition from `Yao.lean` is visible.

## Main definitions

None.

## Main results

* `AliceProgram.selectedKeys_poly`: encoded selected input keys are polynomial-time.
* `AliceProgram.outputPairs_poly`: encoded decoding pairs are polynomial-time.
* `AliceProgram.message_poly`: the complete first garbling message is polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (the first message of Alice).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The encoded list of `keyAt C s v (xs.getD v false)` for `v < count` is polynomial-time
when the unary width/bound/count maps and raw input/coin words are polynomial-time,
`count ≤ inputs`, and the seed satisfies its addressed-key equation.
[PS10, Protocol 162.6], Alice's selected input keys.

**Proof sketch.** On an indexed retained input, the index length is the input vertex and
a polynomial-time bit read selects its input bit. The generic addressed-key contract
computes the corresponding key word. Encode this indexed word vector with the public
range assembler; input-vertex bounds allow the supplied key reader at every genuine index. -/
theorem selectedKeys_poly (width bound count inputs : List Bool → ℕ)
    (xs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hxs : PolyTimeComputable xs) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hcount_le : ∀ z, count z ≤ inputs z)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun v : Fin (count z) =>
      List.ofFn (keyAt (C z) (s z) v ((xs z).getD v false))) := by
  let entry := fun z v => List.ofFn fun t : Fin (width z) => (coins z).getD
    ((((xs z).getD v false).toNat * bound z + v) * width z + t) false
  have hw : PolyTimeComputable fun w => List.replicate (width (pairSndD w)) true :=
    hwidth.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => List.replicate (bound (pairSndD w)) true :=
    hbound.comp polyTimeComputable_pairSndD
  have hbit : PolyTimeComputable fun w =>
      [(xs (pairSndD w)).getD (pairFstD w).length false] :=
    getBit_poly (hxs.comp polyTimeComputable_pairSndD)
      (unaryLength_poly polyTimeComputable_pairFstD)
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length :=
    CoinGarbling.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD) hw hb
      (unaryLength_poly polyTimeComputable_pairFstD) hbit
      (key := fun w (t : Fin (width (pairSndD w))) => (coins (pairSndD w)).getD
        ((((xs (pairSndD w)).getD (pairFstD w).length false).toNat * bound (pairSndD w) +
          (pairFstD w).length) * width (pairSndD w) + t) false) (fun _ _ => rfl)
  refine WordLists.ofFnTable_poly _ entry hcount he ?_
  intro z v
  have hv : (v : ℕ) < (C z).size := by
    rw [DAGCircuit.size_eq]
    have := hcount_le z
    omega
  exact congrArg List.ofFn (hkey z v hv ((xs z).getD v false))

/-- The encoded output-key pairs `⟨keyAt C s (output j) false, keyAt C s (output j) true⟩`
are polynomial-time from a polynomial-time description/coin map, unary width/bound/count
maps, a canonical output-index word list, valid output vertices, and the seed key equation.
[PS10, Protocol 162.6], the output decoding information.

**Proof sketch.** On a unary index, read the corresponding output-index word from the
description's second component. Dropping one symbol from its unary terminated code leaves
a word whose length is the vertex number. The key-window contract computes both Boolean
keys at this vertex. Encode these pairs over the output count; canonical lookup and the
valid-vertex hypotheses identify every pair with the supplied seed's output keys. -/
theorem outputPairs_poly (width bound count inputs : List Bool → ℕ)
    (description coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hcount : PolyTimeComputable fun z => List.replicate (count z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (count z) → ℕ)
    (houtsWord : ∀ z, pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)))
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false) :
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun j : Fin (count z) =>
      pairEncode (List.ofFn (keyAt (C z) (s z) (output z j) false))
        (List.ofFn (keyAt (C z) (s z) (output z j) true))) := by
  let select := fun z j =>
    ((BinArith.getW (pairEncode (List.replicate j true) (pairSndD (description z)))).drop 1).length
  let entry := fun z j => pairEncode
    (RowFromCoins.keyWord width bound (fun v => select v j) (fun _ => false) coins z)
    (RowFromCoins.keyWord width bound (fun v => select v j) (fun _ => true) coins z)
  have hw : PolyTimeComputable fun w => List.replicate (width (pairSndD w)) true :=
    hwidth.comp polyTimeComputable_pairSndD
  have hb : PolyTimeComputable fun w => List.replicate (bound (pairSndD w)) true :=
    hbound.comp polyTimeComputable_pairSndD
  have hlookup := BinArith.polyTimeComputable_getW.comp
    ((polyTimeComputable_unary.comp polyTimeComputable_pairFstD).pairEncode
      ((polyTimeComputable_pairSndD.comp hdescription).comp polyTimeComputable_pairSndD))
  have hv : PolyTimeComputable fun w =>
      List.replicate (select (pairSndD w) (pairFstD w).length) true :=
    unaryLength_poly (polyTimeComputable_tail.comp hlookup)
  have h₀ := RowFromCoins.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD) hw hb hv
    (polyTimeComputable_const [false])
  have h₁ := RowFromCoins.keyWord_poly (hcoins.comp polyTimeComputable_pairSndD) hw hb hv
    (polyTimeComputable_const [true])
  have he : PolyTimeComputable fun w => entry (pairSndD w) (pairFstD w).length := by
    refine (h₀.pairEncode h₁).congr fun w => ?_
    dsimp only [entry]
    rw [RowFromCoins.keyWord_eq, RowFromCoins.keyWord_eq,
      RowFromCoins.keyWord_eq, RowFromCoins.keyWord_eq]
    simp only [Function.comp_apply]
  refine WordLists.ofFnTable_poly _ entry hcount he ?_
  intro z j
  -- The canonical unary code determines the output vertex at this index.
  have hcode : BinArith.getW (pairEncode (List.replicate j true) (pairSndD (description z))) =
      encodeNat (output z j) := by
    rw [houtsWord z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]
  have hvertex : select z j = output z j := by
    dsimp only [select]
    rw [hcode, encodeNat_def, List.length_drop, List.length_append,
      List.length_replicate, List.length_singleton]
    omega
  dsimp only [entry]
  apply congrArg₂ pairEncode
  · rw [RowFromCoins.keyWord_eq, hvertex]
    exact congrArg List.ofFn (hkey z (output z j) (houtput_lt z j) false)
  · rw [RowFromCoins.keyWord_eq, hvertex]
    exact congrArg List.ofFn (hkey z (output z j) (houtput_lt z j) true)

/-- Alice's complete garbling message is polynomial-time: the pair of the actual encoded
nested-special garbled tables and the pair of her selected input-key vector and the output
decoding-pair vector. The hypotheses are polynomial-time raw selectors, canonical uniform
circuit descriptions, valid output vertices, fan-in at most two, and the supplied seed block
and XOR-shift readers. [PS10, Protocol 162.6]

**Proof sketch.** The generic garbling program proves polynomial time for the actual table
vector from description and seed readers. `selectedKeys_poly` gives Alice's input-key vector,
and `outputPairs_poly` gives the decoding-pair vector from the same description. Two public
pairing closure applications assemble the message. -/
theorem message_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs inA outLen : List Bool → ℕ)
    (description xs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hinA : PolyTimeComputable fun z => List.replicate (inA z) true)
    (houtLen : PolyTimeComputable fun z => List.replicate (outLen z) true)
    (hdescription : PolyTimeComputable description) (hxs : PolyTimeComputable xs)
    (hcoins : PolyTimeComputable coins) (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (output : ∀ z, Fin (outLen z) → ℕ)
    (hshape : ∀ z, description z = pairEncode (C z).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (output z j))))
    (hinA_le : ∀ z, inA z ≤ inputs z)
    (houtput_lt : ∀ z j, output z j < (C z).size)
    (hfan : ∀ z (i : Fin (C z).gates.length), ((C z).gates[i]).args.length ≤ 2)
    (hkey : ∀ z (v : ℕ), v < (C z).size → ∀ b,
      keyAt (C z) (s z) v b = fun t : Fin (width z) =>
        (coins z).getD ((b.toNat * bound z + v) * width z + t) false)
    (hr₀ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).1 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + t) false)
    (hr₁ : ∀ z (i : Fin (C z).gates.length) a t, ((s z).2.1 i a).2 t = (coins z).getD
      (2 * bound z * width z +
        (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) *
          (2 * width z) + width z + t) false)
    (hperm : ∀ z (i : Fin (C z).gates.length) a t, (s z).2.2 i a t = xor (a t)
      ((coins z).getD (10 * bound z * width z + 2 * i + t) false)) :
    PolyTimeComputable fun z => pairEncode
      (BinArith.encWords (List.ofFn fun i =>
        BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)))
      (pairEncode
        (BinArith.encWords (List.ofFn fun v : Fin (inA z) =>
          List.ofFn (keyAt (C z) (s z) v ((xs z).getD v false))))
        (BinArith.encWords (List.ofFn fun j : Fin (outLen z) =>
          pairEncode (List.ofFn (keyAt (C z) (s z) (output z j) false))
            (List.ofFn (keyAt (C z) (s z) (output z j) true))))) := by
  have ht := GarblingProgram.tables_poly hE₁ hE₂ width bound inputs description
    (fun z => BinArith.encWords (List.ofFn fun j => encodeNat (output z j))) coins
    hwidth hbound hinputs hdescription hcoins C s hshape hfan hkey hr₀ hr₁ hperm
  have hk := selectedKeys_poly width bound inA inputs xs coins hwidth hbound hinA hxs hcoins
    C s hinA_le hkey
  have houtsWord (z : List Bool) : pairSndD (description z) =
      BinArith.encWords (List.ofFn fun j => encodeNat (output z j)) := by
    rw [hshape z, pairSndD_pairEncode]
  have hp := outputPairs_poly width bound outLen inputs description coins
    hwidth hbound houtLen hdescription hcoins C s output houtsWord houtput_lt hkey
  exact ht.pairEncode (hk.pairEncode hp)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.AliceProgram
