/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Garbling
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FirstTagged
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
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
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
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
# Reconstruction from a tuple of slice ciphertexts

A row descriptor retains a fixed ciphertext, reads one challenge slot, or wraps one challenge
slot under a supplied known outer key. These total word operations never receive the selected
challenge key. Nested public list maps rebuild tables, and fixed advice supplies the other
fields of the view. The same machine handles malformed descriptors and challenge encodings.

## Main definitions

* `SliceReconstruction.fixedRecord`, `directRecord`, `wrappedRecord`: row advice records.
* `SliceReconstruction.row`: the total row interpreter.
* `SliceReconstruction.table`, `tables`: nested table reconstruction.

## Main results

* `SliceReconstruction.row_poly`: polynomial time on every raw word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (embedding all encryptions under one inactive wire key).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction

open Complexity Turing TCSlib.Cryptography

/-- The fixed-row record is `⟨[], c⟩`, retaining ciphertext `c` unchanged. -/
def fixedRecord (c : List Bool) : List Bool := pairEncode [] c

/-- `fixedRecord c = ⟨[], c⟩`. -/
theorem fixedRecord_eq (c : List Bool) : fixedRecord c = pairEncode [] c := rfl

/-- The direct-challenge record is `⟨[true], ⟨1^j, []⟩⟩`, selecting challenge slot `j`. -/
def directRecord (j : ℕ) : List Bool :=
  pairEncode [true] (pairEncode (List.replicate j true) [])

/-- `directRecord j = ⟨[true], ⟨1^j, []⟩⟩`. -/
theorem directRecord_eq (j : ℕ) :
    directRecord j = pairEncode [true] (pairEncode (List.replicate j true) []) := rfl

/-- The wrapped-challenge record is `⟨[false], ⟨1^j, ⟨k,r⟩⟩⟩`, selecting challenge
slot `j` and encrypting it under the supplied known outer key `k` with nonce `r`. -/
def wrappedRecord (j : ℕ) (k r : List Bool) : List Bool :=
  pairEncode [false] (pairEncode (List.replicate j true) (pairEncode k r))

/-- `wrappedRecord j k r = ⟨[false], ⟨1^j, ⟨k,r⟩⟩⟩`. -/
theorem wrappedRecord_eq (j : ℕ) (k r : List Bool) :
    wrappedRecord j k r =
      pairEncode [false] (pairEncode (List.replicate j true) (pairEncode k r)) := rfl

/-- On `⟨challenge, descriptor⟩`, retain a fixed row, read a challenge slot, or wrap that
slot under its known key and nonce. Empty tags select fixed rows; `[true]` selects a direct
slot; every other tag selects wrapping. Out-of-range challenge lookups return `[]`.
[PS10, Theorem 163.7] -/
def row (E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  let descriptor := pairSndD z
  let tag := pairFstD descriptor
  let data := pairSndD descriptor
  let c := (BinArith.decWords (pairFstD z)).getD (pairFstD data).length []
  if tag = [] then data else if tag = [true] then c
  else spEncStr E₂ (pairFstD (pairSndD data)) c (pairSndD (pairSndD data))

/-- `row E₂ z` branches on the descriptor tag and uses the decoded challenge slot at the
unary index stored in its data, with default `[]`. -/
theorem row_eq (E₂ : List Bool → List Bool) (z : List Bool) :
    row E₂ z =
      let descriptor := pairSndD z
      let tag := pairFstD descriptor
      let data := pairSndD descriptor
      let c := (BinArith.decWords (pairFstD z)).getD (pairFstD data).length []
      if tag = [] then data else if tag = [true] then c
      else spEncStr E₂ (pairFstD (pairSndD data)) c (pairSndD (pairSndD data)) := rfl

/-- The row interpreter is polynomial-time for polynomial-time `E₂`, on every raw input.
No selected key is supplied to the interpreter. [PS10, Theorem 163.7]

**Proof sketch.** Normalize the challenge word list and apply the existing polynomial-time
indexed lookup. Descriptor projections give the known wrapping key and nonce. Special
encryption is polynomial-time on these words, and two word-tag tests select the fixed,
direct, or wrapped result. Normalization makes every lookup valid even on malformed inputs. -/
theorem row_poly {E₂ : List Bool → List Bool} (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (row E₂) := by
  have htag := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hdata := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hindex := polyTimeComputable_unary.comp (polyTimeComputable_pairFstD.comp hdata)
  have hchallenge := polyTimeComputable_reencodeWords.comp polyTimeComputable_pairFstD
  have hread := BinArith.polyTimeComputable_getW.comp (hindex.pairEncode hchallenge)
  have hkey := polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hdata)
  have hnonce := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hdata)
  have hwrap := Garbling.spEncStr_poly hE₂ hkey hread hnonce
  have hdirect := polyTimeComputable_pairEq.comp
    (htag.pairEncode (polyTimeComputable_const [true]))
  have h := polyTimeComputable_ite (polyTimeComputable_isNil.comp htag) hdata
    (polyTimeComputable_ite hdirect hread hwrap)
  convert h using 1
  funext z
  simp only [row_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.getW_pairEncode, List.length_replicate, decide_eq_true_eq]

/-- A fixed record reconstructs its retained ciphertext unchanged for every challenge word. -/
theorem row_fixedRecord (E₂ : List Bool → List Bool) (challenge c : List Bool) :
    row E₂ (pairEncode challenge (fixedRecord c)) = c := by
  simp only [row_eq, fixedRecord_eq, pairFstD_pairEncode, pairSndD_pairEncode, ite_true]

/-- Reconstruct an encoded row-descriptor list with one retained challenge tuple. -/
def table (E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinArith.mapW (row E₂) z

/-- `table E₂ z = mapW (row E₂) z`. -/
theorem table_eq (E₂ : List Bool → List Bool) (z : List Bool) :
    table E₂ z = BinArith.mapW (row E₂) z := rfl

/-- Reconstructing one encoded table is polynomial-time on every raw word. -/
theorem table_poly {E₂ : List Bool → List Bool} (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (table E₂) := BinArith.polyTimeComputable_mapW (row_poly hE₂)

/-- On `⟨challenge, descriptors⟩`, reconstruct each decoded row descriptor in order. -/
theorem table_pairEncode (E₂ : List Bool → List Bool) (challenge descriptors : List Bool) :
    table E₂ (pairEncode challenge descriptors) = BinArith.encWords
      ((BinArith.decWords descriptors).map fun d => row E₂ (pairEncode challenge d)) :=
  (table_eq _ _).trans (BinArith.mapW_pairEncode _ _ _)

/-- Reconstruct an encoded list of tables from its encoded lists of row descriptors. -/
def tables (E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinArith.mapW (table E₂) z

/-- `tables E₂ z = mapW (table E₂) z`. -/
theorem tables_eq (E₂ : List Bool → List Bool) (z : List Bool) :
    tables E₂ z = BinArith.mapW (table E₂) z := rfl

/-- Reconstructing all encoded tables is polynomial-time on every raw word. -/
theorem tables_poly {E₂ : List Bool → List Bool} (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (tables E₂) := BinArith.polyTimeComputable_mapW (table_poly hE₂)

/-- On `⟨challenge, descriptors⟩`, reconstruct each decoded table-descriptor list in order. -/
theorem tables_pairEncode (E₂ : List Bool → List Bool) (challenge descriptors : List Bool) :
    tables E₂ (pairEncode challenge descriptors) = BinArith.encWords
      ((BinArith.decWords descriptors).map fun d => table E₂ (pairEncode challenge d)) :=
  (tables_eq _ _).trans (BinArith.mapW_pairEncode _ _ _)

/-- A direct record selects exactly the indexed ciphertext from a canonical challenge list,
using `[]` as the default for an index beyond the list. -/
theorem row_directRecord (E₂ : List Bool → List Bool) (challenge : List (List Bool)) (j : ℕ) :
    row E₂ (pairEncode (BinArith.encWords challenge) (directRecord j)) =
      challenge.getD j [] := by
  simp only [row_eq, directRecord_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.decWords_encWords, List.length_replicate, List.cons_ne_nil, ite_false, ite_true]

/-- A wrapped record encrypts the indexed canonical challenge ciphertext under exactly
the supplied known outer key and nonce. -/
theorem row_wrappedRecord (E₂ : List Bool → List Bool) (challenge : List (List Bool))
    (j : ℕ) (k r : List Bool) :
    row E₂ (pairEncode (BinArith.encWords challenge) (wrappedRecord j k r)) =
      spEncStr E₂ k (challenge.getD j []) r := by
  simp only [row_eq, wrappedRecord_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.decWords_encWords, List.length_replicate, List.cons_ne_nil, List.cons.injEq,
    Bool.false_eq_true, false_and, ite_false]

/-- Fixed reconstruction advice is `⟨tableDescriptors, ⟨messageTail, ⟨privateInput,aliceOut⟩⟩⟩`.
Its fields contain no selected challenge key or challenge nonces. -/
def advice (tableDescriptors messageTail privateInput aliceOut : List Bool) : List Bool :=
  pairEncode tableDescriptors (pairEncode messageTail (pairEncode privateInput aliceOut))

/-- `advice d t x a = ⟨d, ⟨t, ⟨x,a⟩⟩⟩`. -/
theorem advice_eq (d t x a : List Bool) :
    advice d t x a = pairEncode d (pairEncode t (pairEncode x a)) := rfl

/-- On `⟨N,⟨challenge,advice⟩⟩`, reconstruct the tables, append the fixed message tail,
and encode the view with fixed private input, empty tape, and that sole received message.
Pair the view with the retained Alice output. [PS10, Theorem 163.7] -/
def rebuild (E₂ : List Bool → List Bool) (z : List Bool) : List Bool :=
  let data := pairSndD (pairSndD z)
  let rest := pairSndD data
  let message := pairEncode
    (tables E₂ (pairEncode (pairFstD (pairSndD z)) (pairFstD data))) (pairFstD rest)
  pairEncode (⟨pairFstD z, pairFstD (pairSndD rest), [], [message]⟩ : View).encode
    (pairSndD (pairSndD rest))

/-- `rebuild E₂ z` assembles the reconstructed table word and three fixed advice fields
into the encoded view and retained Alice output. -/
theorem rebuild_eq (E₂ : List Bool → List Bool) (z : List Bool) :
    rebuild E₂ z =
      let data := pairSndD (pairSndD z)
      let rest := pairSndD data
      let message := pairEncode
        (tables E₂ (pairEncode (pairFstD (pairSndD z)) (pairFstD data))) (pairFstD rest)
      pairEncode (⟨pairFstD z, pairFstD (pairSndD rest), [], [message]⟩ : View).encode
        (pairSndD (pairSndD rest)) := rfl

/-- Reconstructing the entire encoded view/output endpoint is polynomial-time on every
raw input whenever the known-key outer evaluator is polynomial-time.
[PS10, Theorem 163.7]

**Proof sketch.** Project the challenge tuple and table descriptors, then apply the public
polynomial-time nested table interpreter. Pair its result with the fixed message tail.
The other advice fields supply the private input and Alice output. Polynomial-time pair
assembly encodes the view with empty tape and one received message, then retains Alice's
output as the endpoint's second component. -/
theorem rebuild_poly {E₂ : List Bool → List Bool} (hE₂ : PolyTimeComputable E₂) :
    PolyTimeComputable (rebuild E₂) := by
  have hdata := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hrest := polyTimeComputable_pairSndD.comp hdata
  have hchallenge := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hdescriptors := polyTimeComputable_pairFstD.comp hdata
  have ht := (tables_poly hE₂).comp (hchallenge.pairEncode hdescriptors)
  have htail := polyTimeComputable_pairFstD.comp hrest
  have hprivate := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp hrest)
  have halice := polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hrest)
  have hmessage := ht.pairEncode htail
  have hnil := polyTimeComputable_const ([] : List Bool)
  have hview := (polyTimeComputable_pairFstD.pairEncode hprivate).pairEncode
    (hnil.pairEncode (hmessage.pairEncode hnil))
  refine (hview.pairEncode halice).congr (g := rebuild E₂) fun z => ?_
  simp only [rebuild_eq, View.encode_mk, Function.comp_apply,
    Strategy.encodeMsgs_cons, Strategy.encodeMsgs_nil]

/-- The private-key ciphertext-list encoding is the binary-arithmetic word-list encoding.
This bridge reuses the existing public concatenation characterization. -/
theorem encodeList_eq_encWords (cs : List (List Bool)) :
    PrivateKeyScheme.encodeList cs = BinArith.encWords cs :=
  (TCSlib.Cryptography.encodeList_eq_flatMap cs).trans (BinArith.encWords_def cs).symm

/-- For any challenge word and canonical nested descriptor lists, reconstruct each row
in its original table, preserving the order of both tables and rows. -/
theorem tables_records (E₂ : List Bool → List Bool) (challenge : List Bool)
    (descriptors : List (List (List Bool))) :
    tables E₂ (pairEncode challenge (BinArith.encWords (descriptors.map BinArith.encWords))) =
      BinArith.encWords (descriptors.map fun ds => BinArith.encWords
        (ds.map fun d => row E₂ (pairEncode challenge d))) := by
  simp only [tables_pairEncode, table_pairEncode, BinArith.decWords_encWords, List.map_map]
  apply congrArg BinArith.encWords
  apply List.map_congr_left
  intro ds _
  simp only [Function.comp_apply, BinArith.decWords_encWords]

/-- On canonical challenge and descriptor lists, reconstruction retains table and row order. -/
theorem tables_encoded (E₂ : List Bool → List Bool) (challenge : List (List Bool))
    (descriptors : List (List (List Bool))) :
    tables E₂ (pairEncode (BinArith.encWords challenge)
      (BinArith.encWords (descriptors.map BinArith.encWords))) =
        BinArith.encWords (descriptors.map fun ds => BinArith.encWords
          (ds.map fun d => row E₂ (pairEncode (BinArith.encWords challenge) d))) :=
  tables_records E₂ (BinArith.encWords challenge) descriptors

/-- The fixed, direct, and wrapped record lengths are respectively `|c|+2`, `2j+6`, and
`2j+2|k|+|r|+8`. Thus a unary challenge index and the known words give explicit advice costs. -/
theorem record_lengths (c : List Bool) (j : ℕ) (k r : List Bool) :
    (fixedRecord c).length = c.length + 2 ∧
      (directRecord j).length = 2 * j + 6 ∧
      (wrappedRecord j k r).length = 2 * j + 2 * k.length + r.length + 8 := by
  simp only [fixedRecord_eq, directRecord_eq, wrappedRecord_eq, length_pairEncode,
    List.length_nil, List.length_cons, List.length_replicate]
  omega

/-- Fixed surrounding advice has length `2|d|+2|t|+2|x|+|a|+6`, where the fields are
table descriptors, message tail, private input, and retained Alice output. -/
theorem advice_length (d t x a : List Bool) :
    (advice d t x a).length = 2 * d.length + 2 * t.length + 2 * x.length + a.length + 6 := by
  rw [advice_eq]
  simp only [length_pairEncode]
  omega

/-- On its canonical layout, reconstruction returns the view with reconstructed tables,
fixed message tail and private input, paired with the fixed actual Alice output. -/
theorem rebuild_layout (E₂ : List Bool → List Bool) (N challenge d t x a : List Bool) :
    rebuild E₂ (pairEncode N (pairEncode challenge (advice d t x a))) =
      pairEncode
        (⟨N, x, [], [pairEncode (tables E₂ (pairEncode challenge d)) t]⟩ : View).encode a := by
  simp only [rebuild_eq, advice_eq, pairFstD_pairEncode, pairSndD_pairEncode]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SliceReconstruction
