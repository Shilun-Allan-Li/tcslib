/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.AllTables
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.DescriptionDecoder

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generic garbling programs from uniform circuit descriptions

The interface takes a circuit family, a polynomial-time description map, numeric/coin maps,
and a seed satisfying its key, row-nonce, and XOR-shift block equations. It does not refer
to any definition from `Yao.lean`.

## Main definitions

* `GarblingProgram.gatesWord`: the gate-record word extracted by the public decoder.

## Main results

* `GarblingProgram.tables_poly`: polynomial time for the actual encoded garbled tables.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Protocol 162.6 (garbling the canonical uniform circuit).
* [BMR90] D. Beaver, S. Micali, P. Rogaway, *The round complexity of secure protocols*,
  STOC 1990, pp. 503–513 (point-and-permute row order of the garbled tables).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The gate-record list extracted from a circuit-description pair:
`gatesWord description z = pairSndD (readCircuit (pairFstD (description z)))`. -/
def gatesWord (description : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairSndD (DescriptionDecoder.readCircuit (pairFstD (description z)))

/-- `gatesWord description z = pairSndD (readCircuit (pairFstD (description z)))`. -/
theorem gatesWord_eq (description : List Bool → List Bool) (z : List Bool) :
    gatesWord description z =
      pairSndD (DescriptionDecoder.readCircuit (pairFstD (description z))) := rfl

/-- Extracting the gate-record word is polynomial-time from a polynomial-time description.
`PolyTimeComputable (gatesWord description)`. -/
theorem gatesWord_poly {description : List Bool → List Bool}
    (hdescription : PolyTimeComputable description) : PolyTimeComputable (gatesWord description) :=
  polyTimeComputable_pairSndD.comp
    (DescriptionDecoder.readCircuit_poly.comp (polyTimeComputable_pairFstD.comp hdescription))

/-- A canonical description gives exactly its encoded gate-record list:
`gatesWord description z = encWords (C.gates.map gateRecord)`. -/
theorem gatesWord_description (description : List Bool → List Bool) (z : List Bool)
    {m : ℕ} (C : DAGCircuit m) (outs : List Bool)
    (hdescription : description z = pairEncode C.encode outs) :
    gatesWord description z = BinArith.encWords (C.gates.map DescriptionDecoder.gateRecord) := by
  rw [gatesWord_eq, hdescription, pairFstD_pairEncode,
    DescriptionDecoder.readCircuit_encode, pairSndD_pairEncode]

/-- The actual encoded garbled-table vector is polynomial-time from a polynomial-time
circuit-description pair, polynomial-time unary/coin maps, fan-in at most two, and the
supplied seed's key, row-nonce, and XOR-shift equations. [PS10, Protocol 162.6; BMR90]
`PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i => BinArith.encWords (garbledTable
(nestedSpecial E₁ E₂ (width z)) (C z) (s z) i))`.

**Proof sketch.** Decode the description to its gate-record word and apply the total raw
all-table machine. At a canonical index, the public context-transport equation exposes the
selected gate record. Canonical list lookup supplies its kind and unary argument words.
The row-machine seed contract identifies every encrypted row, the table contract identifies
the enumerated table, and the outer word-vector contract identifies the complete table list.
No unproved indexed reconstruction hypothesis is left to the consumer. -/
theorem tables_poly {E₁ E₂ : List Bool → List Bool} (hE₁ : PolyTimeComputable E₁)
    (hE₂ : PolyTimeComputable E₂) (width bound inputs : List Bool → ℕ)
    (description outs coins : List Bool → List Bool)
    (hwidth : PolyTimeComputable fun z => List.replicate (width z) true)
    (hbound : PolyTimeComputable fun z => List.replicate (bound z) true)
    (hinputs : PolyTimeComputable fun z => List.replicate (inputs z) true)
    (hdescription : PolyTimeComputable description) (hcoins : PolyTimeComputable coins)
    (C : ∀ z, DAGCircuit (inputs z))
    (s : ∀ z, GarbleSeed (C z) (Fin (width z) → Bool)
      ((Fin (width z) → Bool) × (Fin (width z) → Bool)))
    (hshape : ∀ z, description z = pairEncode (C z).encode (outs z))
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
    PolyTimeComputable fun z => BinArith.encWords (List.ofFn fun i =>
      BinArith.encWords (garbledTable (nestedSpecial E₁ E₂ (width z)) (C z) (s z) i)) := by
  let gates := gatesWord description
  have hgates : PolyTimeComputable gates := gatesWord_poly hdescription
  have hgs (z : List Bool) :
      gates z = BinArith.encWords ((C z).gates.map DescriptionDecoder.gateRecord) :=
    gatesWord_description description z (C z) (outs z) (hshape z)
  have hraw := AllTables.allTablesWord_poly hE₁ hE₂ hwidth hbound hinputs hgates hcoins
  refine hraw.congr fun z => ?_
  refine AllTables.allTablesWord_garbledTables E₁ E₂ width bound inputs gates coins
    DescriptionDecoder.gateRecord z (C z) (s z) (hgs z) ?_
  intro i
  -- Transport the indexed context before reading the selected canonical gate record.
  rw [AllTables.entryWord_pair]
  have hrecord : BinArith.getW (pairEncode (List.replicate i true) (gates z)) =
      DescriptionDecoder.gateRecord ((C z).gates[i]) := by
    rw [hgs z, BinArith.getW_pairEncode, List.length_replicate]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact i.isLt), List.getElem_map]
    rfl
  have hk : pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates z))) =
      ((C z).gates[i]).kind.encode := by
    rw [hrecord, DescriptionDecoder.gateRecord_eq, pairFstD_pairEncode]
  have ha : pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates z))) =
      BinArith.encWords (((C z).gates[i]).args.map fun v => List.replicate v true) := by
    rw [hrecord, DescriptionDecoder.gateRecord_eq, pairSndD_pairEncode]
  -- The seed equations supply the entire row-to-table semantic contract.
  refine TablesFromCoins.tableWord_garbledTable E₁ E₂ width bound inputs (fun _ => i)
    (fun v => pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    (fun v => pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    coins z (C z) (s z) i (hfan z i) ha ?_
  intro a
  exact RowFromCoins.rowWord_garbledRow E₁ E₂ width bound inputs (fun _ => i)
    (fun v => pairFstD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    (fun v => pairSndD (BinArith.getW (pairEncode (List.replicate i true) (gates v))))
    coins z (C z) (s z) i a (hfan z i) rfl hk ha (hkey z) (hr₀ z i) (hr₁ z i) (hperm z i)

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.GarblingProgram
