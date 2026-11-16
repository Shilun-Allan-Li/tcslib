/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedPlan
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.Lengths
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.GateHybrids
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.SelectedFields
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
# Exact selected-key table and view reconstruction

Every challenge message, record and surrounding field is fixed before the sampled key and
nonce vector are supplied. Reconstruction uses every occurrence of the selected inactive
label, including occurrences at gates outside the gate currently switched by the hybrid.
The plaintext-key family is a generic fixed parameter, specialized through the shared
hybrid objects' public contracts. No protocol-specific circuit or strategy definition occurs here.

## Main definitions

None.

## Main results

* `SelectedTables.record_reconstruct`: exact reconstruction for every sampler seed.
* Complete table and encoded-view reconstruction from the padded slice experiment.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (joint multi-message embedding under one inactive key).
* [LP09] Y. Lindell, B. Pinkas, *A proof of security of Yao's protocol for two-party
  computation*, Journal of Cryptology 22(2), 2009, pp. 161–188.
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables

open Complexity Turing BoolCircuit TCSlib.Cryptography

section Joint

variable {L L₂ : ℕ → ℕ}
  (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))
  (G₁ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (n + n) → Bool))
  (G₂ : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L₂ n) → Bool))
  (E₁ E₂ : List Bool → List Bool)
  (hG : ∀ n (s x : Fin n → Bool),
    List.ofFn (G n s x) = List.ofFn (G₁ n s x) ++ List.ofFn (G₂ n s x))
  (hGE₁ : ∀ n (s x : Fin n → Bool), E₁ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₁ n s x))
  (hGE₂ : ∀ n (s x : Fin n → Bool), E₂ (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (G₂ n s x))

include hG hGE₁ hGE₂ in
/-- Every row record reconstructs precisely the nested encryption using the filled seed's
argument keys and nonce pair and the fixed plaintext key, for every challenge key and nonce
vector. The capacity covers the complete all-gate occurrence list. [PS10, Theorem 163.7]

**Proof sketch.** An unselected row retains both its argument-key list and nonce pair, so its
fixed record is already the required row. For a selected argument, its occurrence rank fits
the padded capacity. Reading that slot recovers the row's exact slice shape and precomputed
message. The selected-row reconstruction theorem replaces precisely the argument key and
nonce half described by the filled-seed readers. All gates using the selected key share this
same sampler key while receiving their own independent slot nonce. -/
theorem record_reconstruct {m n : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hfan : ∀ i : Fin C.gates.length, C.gates[i.val].args.length ≤ 2)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool)
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) :
    SliceReconstruction.row E₂ (pairEncode
      (sliceMultiEncDist G n q (SelectedPlan.slotOffset C rows s u q)
        (SelectedPlan.slotLength C rows s u q) (SelectedPlan.slotMessage C rows s u q E₁ o)
          (k, rs)) (SelectedPlan.record C rows s u E₁ E₂ o i a)) =
      (nestedSpecial E₁ E₂ n).enc (argKeys C (SelectedSeed.fill C rows s u q k rs) i a)
        (o i a) ((SelectedSeed.fill C rows s u q k rs).2.1 i a) := by
  cases hsel : GateOccurrences.selectedPosition C.gates[i.val] a u.val with
  | none =>
    rw [SelectedPlan.record_eq, hsel, Option.elim_none, SliceReconstruction.row_fixedRecord,
      SelectedSeed.fill_argKeys_none C rows s u q k rs i a (hargs i) hsel,
      SelectedSeed.fill_nonce, SelectedSeed.nonce_of_none C rows s u.val q rs i a hsel]
  | some p =>
    obtain ⟨hvertex, hbit⟩ :=
      (GateOccurrences.selectedPosition_eq_some_iff _ _ _ (hargs i) p).mp hsel
    have hslot := lt_of_lt_of_le
      (SelectedSeed.slotIndex_lt C rows s.2.2 u.val i a p (hargs i)
        (hcomplete i) hvertex hbit) hcap
    let j : Fin (q + 1) := ⟨SelectedSeed.slotIndex C rows s.2.2 u.val i a p, hslot⟩
    have hpad := SelectedSeed.slotIndex_padded C rows s.2.2 u.val q i a p (hargs i)
      (hcomplete i) hvertex hbit hslot
    have hread := SelectedPlan.slotReaders_of_padded C rows s u q E₁ o j i
      (SelectedSeed.rowIndex C rows s.2.2 i a) p.val hpad
    have hactual := SelectedSeed.rowIndex_actual C rows s.2.2 i a (hcomplete i)
    obtain ⟨hOff, _, hWord⟩ := hread
    have hOff' := hOff.trans (congrArg
      (fun b => SelectedRows.offset n (argKeys C s i b) p.val) hactual)
    have hWord' := hWord.trans (congrArg
      (fun b => SelectedRows.word E₁ n (argKeys C s i b) (o i b) (s.2.1 i b) p.val) hactual)
    have hMsg := (SelectedPlan.slotMessage_ofFn C rows s u q hGE₁ o j).trans hWord'
    have hlen : (argKeys C s i a).length = C.gates[i.val].args.length := by
      simp only [argKeys_eq, List.length_ofFn, Fin.getElem_fin]
    have hks : (argKeys C s i a).length ≤ 2 := by rw [hlen]; exact hfan i
    have hp : p.val < (argKeys C s i a).length := by rw [hlen]; exact p.isLt
    rw [SelectedPlan.record_eq, hsel, Option.elim_some,
      SelectedSeed.fill_argKeys_some C rows s u q k rs i a p (hargs i) hsel,
      SelectedSeed.fill_nonce, SelectedSeed.nonce_of_some C rows s u.val q rs i a p hsel hslot]
    exact SelectedRows.reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ n q (argKeys C s i a)
      (o i a) (s.2.1 i a) p.val j hks hp (SelectedPlan.slotOffset C rows s u q)
      (SelectedPlan.slotLength C rows s u q) (SelectedPlan.slotMessage C rows s u q E₁ o)
      hOff' hMsg k rs

include hG hGE₁ hGE₂ in
/-- Reconstructing all descriptor tables yields exactly every filled-seed row in the original
gate and permuted-row order, for every slice-sampler key and nonce vector.
[PS10, Theorem 163.7]

**Proof sketch.** The public nested-list reconstruction contract maps each stored descriptor
in place. The descriptor table reader exposes the original gate-index and row enumerations.
Apply the exact row reconstruction identity at every enumerated assignment. No gate using
the selected key is omitted from the common slice experiment. -/
theorem tables_reconstruct {m n : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool))
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hfan : ∀ i : Fin C.gates.length, C.gates[i.val].args.length ≤ 2)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) :
    SliceReconstruction.tables E₂ (pairEncode
      (sliceMultiEncDist G n q (SelectedPlan.slotOffset C rows s u q)
        (SelectedPlan.slotLength C rows s u q) (SelectedPlan.slotMessage C rows s u q E₁ o)
          (k, rs))
      (BinArith.encWords ((SelectedPlan.tables C rows s u E₁ E₂ o).map BinArith.encWords))) =
      BinArith.encWords (List.ofFn fun i => BinArith.encWords ((rows i).map fun a =>
        (nestedSpecial E₁ E₂ n).enc
          (argKeys C (SelectedSeed.fill C rows s u q k rs) i (s.2.2 i a))
          (o i (s.2.2 i a)) ((SelectedSeed.fill C rows s u q k rs).2.1 i (s.2.2 i a)))) := by
  rw [SliceReconstruction.tables_records, SelectedPlan.tables_eq, List.map_ofFn]
  apply congrArg BinArith.encWords
  apply congrArg List.ofFn
  funext i
  apply congrArg BinArith.encWords
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  exact record_reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ C rows s u q o
    hargs hfan hcomplete hcap i (s.2.2 i a) k rs

include hG hGE₁ hGE₂ in
/-- With canonical row enumeration, reconstruction gives the shared generic hybrid tables.
The fixed plaintext family is read from the original seed; symbolic output-label separation
identifies it with the filled seed's output keys. [PS10, Theorem 163.7]

**Proof sketch.** Apply the complete table reconstruction theorem using the original seed's
output keys as fixed plaintexts. The canonical enumeration is the hybrid table's enumeration.
For each row, the filled permutation is unchanged and output-label separation makes its
plaintext key unchanged. The published hybrid-row reader then identifies the ciphertext. -/
theorem tablesWith_reconstruct {m n : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (bit : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → Bool)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hfan : ∀ i : Fin C.gates.length, C.gates[i.val].args.length ≤ 2)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrows : ∀ i, rows i = (Finset.univ : Finset (Fin C.gates[i.val].args.length → Bool)).toList)
    (hlabel : ∀ i a, (m + i.val, bit i a) ≠ (u.val, true))
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) :
    SliceReconstruction.tables E₂ (pairEncode
      (sliceMultiEncDist G n q (SelectedPlan.slotOffset C rows s u q)
        (SelectedPlan.slotLength C rows s u q)
        (SelectedPlan.slotMessage C rows s u q E₁
          (fun i a => keyAt C s (m + i.val) (bit i a))) (k, rs))
      (BinArith.encWords ((SelectedPlan.tables C rows s u E₁ E₂
        (fun i a => keyAt C s (m + i.val) (bit i a))).map BinArith.encWords))) =
      BinArith.encWords (List.ofFn fun i => BinArith.encWords
        (GateHybrids.tableWith (nestedSpecial E₁ E₂ n) C
          (SelectedSeed.fill C rows s u q k rs) bit i)) := by
  let o : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → (Fin n → Bool) :=
    fun i a => keyAt C s (m + i.val) (bit i a)
  have ht := tables_reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ C rows s u q o
    hargs hfan hcomplete hcap k rs
  refine ht.trans ?_
  apply congrArg BinArith.encWords
  apply congrArg List.ofFn
  funext i
  rw [GateHybrids.tableWith_eq, ← hrows i]
  apply congrArg BinArith.encWords
  apply List.map_congr_left
  intro a _
  rw [GateHybrids.rowWith_eq, SelectedSeed.fill_perm, SelectedSeed.fill_keyAt,
    if_neg (hlabel i (s.2.2 i a))]

include hG hGE₁ hGE₂ in
/-- The total reconstruction machine returns the encoded view/output endpoint with the
filled seed's generic hybrid tables and the supplied fixed surrounding fields.
[PS10, Theorem 163.7]

**Proof sketch.** The reconstruction layout reader retains the supplied common input,
private input, message tail and Alice output. Substitute the exact shared hybrid-table
reconstruction identity into its sole received message. This is a pointwise sampler identity,
with no distributional or computational hypothesis left for the table reconstruction. -/
theorem view_reconstruct {m n : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ)
    (bit : (i : Fin C.gates.length) → (Fin C.gates[i.val].args.length → Bool) → Bool)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hfan : ∀ i : Fin C.gates.length, C.gates[i.val].args.length ≤ 2)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrows : ∀ i, rows i = (Finset.univ : Finset (Fin C.gates[i.val].args.length → Bool)).toList)
    (hlabel : ∀ i a, (m + i.val, bit i a) ≠ (u.val, true))
    (N tail privateInput aliceOutput : List Bool)
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) :
    SliceReconstruction.rebuild E₂ (pairEncode N (pairEncode
      (sliceMultiEncDist G n q (SelectedPlan.slotOffset C rows s u q)
        (SelectedPlan.slotLength C rows s u q)
        (SelectedPlan.slotMessage C rows s u q E₁
          (fun i a => keyAt C s (m + i.val) (bit i a))) (k, rs))
      (SliceReconstruction.advice
        (BinArith.encWords ((SelectedPlan.tables C rows s u E₁ E₂
          (fun i a => keyAt C s (m + i.val) (bit i a))).map BinArith.encWords))
        tail privateInput aliceOutput))) =
      pairEncode (⟨N, privateInput, [], [pairEncode
        (BinArith.encWords (List.ofFn fun i => BinArith.encWords
          (GateHybrids.tableWith (nestedSpecial E₁ E₂ n) C
            (SelectedSeed.fill C rows s u q k rs) bit i))) tail]⟩ : View).encode aliceOutput := by
  rw [SliceReconstruction.rebuild_layout]
  exact congrArg (fun tableCode =>
    pairEncode (⟨N, privateInput, [], [pairEncode tableCode tail]⟩ : View).encode aliceOutput)
    (tablesWith_reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ C rows s u q bit
      hargs hfan hcomplete hcap hrows hlabel k rs)

include hG hGE₁ hGE₂ in
/-- The padded slice experiment reconstructs the actual shared hybrid view sampler under
the filled seed, with empty Bob coins and the retained Alice output. All fixed fields are
computed from the original seed. [PS10, Theorem 163.7]

**Proof sketch.** Reconstruct the filled-seed tables using the stage-bit plaintext family.
False active answers are unchanged by selected fill. Output vertices differ from the selected
wire, so both entries of every decoding pair, and hence the complete message tail, remain
unchanged. The public message and sample readers assemble exactly the reconstructed view. -/
theorem sample_reconstruct {m n : ℕ} (C : DAGCircuit m)
    (rows : (i : Fin C.gates.length) → List (Fin C.gates[i.val].args.length → Bool))
    (s : GarbleSeed C (Fin n → Bool) ((Fin n → Bool) × (Fin n → Bool)))
    (u : Fin C.size) (q : ℕ) (inA inB outLen : ℕ) (output : Fin outLen → ℕ)
    (v : ℕ → Bool) (stage : ℕ) (N bobInput aliceOutput : List Bool)
    (hargs : ∀ i : Fin C.gates.length, C.gates[i.val].args.Nodup)
    (hfan : ∀ i : Fin C.gates.length, C.gates[i.val].args.length ≤ 2)
    (hcomplete : ∀ i a, a ∈ rows i)
    (hcap : (GateOccurrences.occurrences C rows s.2.2 u.val).length ≤ q + 1)
    (hrows : ∀ i, rows i = (Finset.univ : Finset (Fin C.gates[i.val].args.length → Bool)).toList)
    (hlabel : ∀ (i : Fin C.gates.length) (a : Fin C.gates[i.val].args.length → Bool),
      (m + i.val, GateHybrids.stageBit C v stage i a) ≠ (u.val, true))
    (hOut : ∀ j, output j ≠ u.val)
    (k : Fin n → Bool) (rs : Fin (q + 1) → Fin n → Bool) :
    SliceReconstruction.rebuild E₂ (pairEncode N (pairEncode
      (sliceMultiEncDist G n q (SelectedPlan.slotOffset C rows s u q)
        (SelectedPlan.slotLength C rows s u q)
        (SelectedPlan.slotMessage C rows s u q E₁ (fun i a =>
          keyAt C s (m + i.val) (GateHybrids.stageBit C v stage i a))) (k, rs))
      (SelectedPlan.advice C rows s u E₁ E₂ (fun i a =>
        keyAt C s (m + i.val) (GateHybrids.stageBit C v stage i a))
        (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s
          inA outLen output v stage))
        (pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB))) aliceOutput))) =
      GateHybridMessage.sample (nestedSpecial E₁ E₂ n) C (SelectedSeed.fill C rows s u q k rs)
        inA inB outLen output v N bobInput [] aliceOutput stage := by
  rw [SelectedPlan.advice_eq]
  refine (view_reconstruct G G₁ G₂ E₁ E₂ hG hGE₁ hGE₂ C rows s u q
    (GateHybrids.stageBit C v stage) hargs hfan hcomplete hcap hrows hlabel N
    (pairSndD (GateHybridMessage.message (nestedSpecial E₁ E₂ n) C s
      inA outLen output v stage))
    (pairEncode bobInput (List.ofFn (FakeObjects.activeAnswers C s inA inB)))
    aliceOutput k rs).trans ?_
  rw [GateHybridMessage.sample_eq, SelectedFields.activeAnswers_fill]
  rw [← SelectedFields.message_tail_fill (nestedSpecial E₁ E₂ n) C rows s u q k rs
    inA outLen output v stage hOut]
  simp only [GateHybridMessage.message_eq, pairSndD_pairEncode]

end Joint

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.SelectedTables
