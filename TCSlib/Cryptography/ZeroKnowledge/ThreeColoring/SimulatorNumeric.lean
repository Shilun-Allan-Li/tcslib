/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol
import TCSlib.Cryptography.ZeroKnowledge.EncodingPermutations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The 3-colouring simulator: shadows and numeric models

The first half of the machine infrastructure behind Claim-128.a of
`ThreeColoring/Simulator.lean` (`exists_colSimulator`). The frozen string definitions of the
main file (`colSimBlock`, `colSimCoins`, `pair6Equiv`, `sampleColorPair`, `colSimAttemptStr`,
`colSim`, together with the typed `ColorPair` and `simColors` they use) are *shadowed* here by
`ColSimMachine.blockPoly`, `simCoins`, `pair6Equiv`, `sampleColorPair`, `attemptStr`, `sim`,
`ColorPair`, `simColors` with identical bodies, so that the machine can be built before the
main file; the main file identifies each shadow with its original by `rfl`.

The *numeric* layer identifies every typed ingredient of one attempt of
[PS10, Algorithm 128.7] with a number or a string computed from the tape: the rejection
samplers of the edge index and of the colour pair are the first accepted trial of
`EncodingPermutations.trialIdx` and its block value (`sampleNum`, `sampleIdx_eq`); the edge
list of the decoded graph is the list of set bits of the adjacency word in row-major order
(`edgeList_eq_map`), so `|E|` is a bit count (`edgeCount_eq_countBits`) and the `e`-th edge is
the position of the `(e+1)`-th set bit (`edgeOf_val_eq`); one attempt is its numeric form
`attemptNum` (`attemptStr_eq_attemptNum`). The machines themselves are in
`ThreeColoring/SimulatorMachine.lean`.

## Main definitions

* `TCSlib.Cryptography.ColSimMachine.blockPoly`, `simCoins`, `attemptStr`, `sim` — shadows of
  the string simulator of the main file.
* `TCSlib.Cryptography.ColSimMachine.sampleNum`, `countBits`, `edgePos` — the numeric models
  of the rejection sampler, of `|E|` and of the `e`-th edge.
* `TCSlib.Cryptography.ColSimMachine.attemptNum` — one attempt in numeric form, with its
  ingredients `nV`, `mE`, `eIdx`, `vIdx`, `kPos`, `colorNum`, `rrStr`, `comStr`, `rVStr`,
  `opnStr`.

## Main results

* `TCSlib.Cryptography.ColSimMachine.sampleIdx_eq`, `edgeCount_eq_countBits`,
  `edgeOf_val_eq` — the numeric models agree with the typed definitions.
* `TCSlib.Cryptography.ColSimMachine.attemptStr_eq_attemptNum` — one attempt of the string
  simulator is its numeric form.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7 Algorithm 128.7, p. 128.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.ColSimMachine

open Complexity Turing Complexity.StateLoop EncodingMachines

/-! ### Shadows of the typed colour pairs and of the string simulator -/

/-- Shadow of `ColorPair`: the ordered pairs of distinct colours. -/
abbrev ColorPair : Type := {p : Fin 3 × Fin 3 // p.1 ≠ p.2}

/-- There are six distinct colour pairs. -/
theorem card_colorPair : Fintype.card ColorPair = 6 := by decide

/-- Shadow of `simColors`: the guessed pair at the endpoints of `p`, the colour `0` elsewhere. -/
def simColors {n : ℕ} (p : Fin n × Fin n) (ab : ColorPair) : Fin n → Fin 3 :=
  fun k => if k = p.1 then ab.1.1 else if k = p.2 then ab.1.2 else 0

/-- Shadow of `colSimBlock`: the coin block of one attempt against `V'` at instance length
`N` has `(N+1)²` edge-sampling bits, `3N` colour-pair bits, `N ℓ(N)` commitment bits and the
tape of `V'`. -/
def blockPoly (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .add (.add (.add (.normal 1 2) (.mul (.const 3) .var)) (.mul .var ℓ)) V'.coins

/-- Shadow of `colSimCoins`: `N²` blocks. -/
def simCoins (ℓ : PolyExpr) (V' : Strategy) : PolyExpr :=
  .mul (.mul .var .var) (blockPoly ℓ V')

/-- Shadow of `pair6Equiv`: the six distinct colour pairs enumerated by `Fin 6`. -/
noncomputable def pair6Equiv : Fin 6 ≃ ColorPair := (Fintype.equivFinOfCardEq card_colorPair).symm

/-- Shadow of `sampleColorPair`: `T` rejection trials of three bits, the pair `(0, 1)` on
failure. -/
noncomputable def sampleColorPair (T : ℕ) (r : List Bool) : ColorPair :=
  ((sampleIdx 6 3 T r).map pair6Equiv).getD ⟨(0, 1), by decide⟩

/-- Shadow of `colSimAttemptStr`: one attempt of [PS10, Algorithm 128.7] on the coin block
`blk`. -/
noncomputable def attemptStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  let n := (decGraph x).1
  let G : Graph n := (decGraph x).2
  let m := edgeCount G
  let N := x.length
  let e' := sampleEdgeIdx m N blk
  let ab := sampleColorPair N (blk.drop ((N + 1) ^ 2))
  let rr : Fin n → Fin (ℓ.eval n) → Bool :=
    fun i j => blk.getD ((N + 1) ^ 2 + 3 * N + i * ℓ.eval n + j) false
  let rV := blk.drop ((N + 1) ^ 2 + 3 * N + N * ℓ.eval N)
  match edgeAt G e' with
  | none => some (View.encode ⟨x, z, rV, [colCommit Com n (ℓ.eval n) (fun _ => 0) rr, []]⟩)
  | some p =>
    let c' := simColors p ab
    let com := colCommit Com n (ℓ.eval n) c' rr
    if edgeIdxOfMsg m (V'.next x z rV [com]) = e' then
      some (View.encode ⟨x, z, rV, [com, colOpen c' rr p]⟩)
    else none

/-- Shadow of `colSim`: up to `n|E|` attempts on consecutive coin blocks, the first successful
view, or `[]`; a single attempt if `E = ∅`. -/
noncomputable def sim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z r : List Bool) : List Bool :=
  let B := (blockPoly ℓ V').eval x.length
  let att : ℕ → Option (List Bool) := fun t => attemptStr Com ℓ V' x z (colCoinSlice B t r)
  if edgeCount (decGraph x).2 = 0 then (att 0).getD []
  else ((List.range (colIterations x)).findSome? att).getD []

/-! ### The numeric model of the rejection samplers -/

/-- The `k` bits of the tape from position `base` read as a number: `bitsToNat` of the block
is `EncodingMachines.blockVal` (induction on `k`, `List.ofFn_succ'`, `blockVal_succ`). -/
theorem bitsToNat_getD_eq_blockVal (r : List Bool) (base : ℕ) :
    ∀ k, bitsToNat (fun j : Fin k => r.getD (base + j) false) = blockVal r base k
  | 0 => by simp [bitsToNat]
  | k + 1 => by
    rw [blockVal_succ, ← bitsToNat_getD_eq_blockVal r base k]
    unfold bitsToNat
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append, List.foldl_cons, List.foldl_nil]
    simp only [Fin.coe_castSucc, Fin.val_last]
    congr 1
    rw [show (r.getD (base + k) false).toNat = cond (r.getD (base + k) false) 1 0 from rfl,
      Bool.cond_eq_ite]

/-- `List.findSome?` over `List.range T` is the value at the first index with a `some`, if any
(`EncodingMachines.firstIdx` on the `isSome` test).

**Proof sketch.** Induction on `T` through `List.range_succ` and `List.findSome?_append`: if
the search over `range T` succeeds, appending `T` changes neither the search index
(`firstIdx_eq_of`, `firstIdx_min`) nor the result; otherwise every `t < T` is rejected
(`firstIdx_eq_iff`), the result is `g T`, and the search index over `T + 1` is `T` or `T + 1`
according to `(g T).isSome`. -/
theorem findSome?_range_eq {α : Type*} (g : ℕ → Option α) (T : ℕ) :
    (List.range T).findSome? g =
      if firstIdx (fun t => (g t).isSome) T < T then g (firstIdx (fun t => (g t).isSome) T)
      else none := by
  induction T with
  | zero => simp [firstIdx]
  | succ T ih =>
    rw [List.range_succ, List.findSome?_append, ih, List.findSome?_singleton]
    by_cases h : firstIdx (fun t => (g t).isSome) T < T
    · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = firstIdx (fun t => (g t).isSome) T :=
        firstIdx_eq_of (Nat.lt_succ_of_lt h) (q_firstIdx h) fun i hi => firstIdx_min hi
      rw [if_pos h, heq, if_pos (Nat.lt_succ_of_lt h)]
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (q_firstIdx h)
      rw [hv]
      rfl
    · rw [if_neg h, Option.none_or]
      have hall : ∀ i < T, (g i).isSome = false :=
        firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
      by_cases hT : (g T).isSome = true
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T :=
          firstIdx_eq_of (Nat.lt_succ_self T) hT hall
        rw [heq, if_pos (Nat.lt_succ_self T)]
      · have heq : firstIdx (fun t => (g t).isSome) (T + 1) = T + 1 :=
          firstIdx_eq_of_forall fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
            · exact hall i hi
            · simpa using hT
        rw [heq, if_neg (lt_irrefl _)]
        cases hg : g T with
        | none => rfl
        | some v => simp [hg] at hT

/-- The numeric model of the rejection sampler `sampleIdx m k T r`: the block value of the
first accepted trial (the first `t < T` whose `k`-bit block reads below `m`), and `m` itself
(an out-of-range marker) if every trial is rejected. -/
noncomputable def sampleNum (m k T : ℕ) (r : List Bool) : ℕ :=
  if trialIdx m k T r 0 < T then blockVal r (trialIdx m k T r 0 * k) k else m

/-- **The rejection sampler is its numeric model**: `sampleIdx m k T r` is `some` of the
numeric sample when it is below `m` and `none` otherwise.

**Proof sketch.** `sampleIdx` is `List.findSome?` over `List.finRange T` of the trials, i.e.
over `List.range T` (`List.map_coe_finRange`, `List.findSome?_map`); each trial is `some` of
its block value iff that value is below `m` (`uniformFromBits`, `bitsToNat_getD_eq_blockVal`);
`findSome?_range_eq` turns the search into `trialIdx m k T r 0` (`firstIdx_congr`). -/
theorem sampleIdx_eq (m k T : ℕ) (r : List Bool) :
    sampleIdx m k T r =
      if h : sampleNum m k T r < m then some ⟨sampleNum m k T r, h⟩ else none := by
  set g : ℕ → Option (Fin m) := fun t =>
    if h : blockVal r (t * k) k < m then some ⟨blockVal r (t * k) k, h⟩ else none with hg
  have h1 : sampleIdx m k T r = (List.range T).findSome? g := by
    show (List.finRange T).findSome? (fun t : Fin T =>
      uniformFromBits m k (fun j : Fin k => r.getD ((t : ℕ) * k + j) false)) = _
    rw [← List.map_coe_finRange, List.findSome?_map]
    congr 1
    funext t
    simp only [Function.comp, uniformFromBits, hg, bitsToNat_getD_eq_blockVal]
  have h2 : ∀ t, (g t).isSome = decide (blockVal r ((0 * T + t) * k) k < m - 0) := by
    intro t
    simp only [hg, zero_mul, zero_add, Nat.sub_zero]
    split_ifs <;> simp_all
  rw [h1, findSome?_range_eq, firstIdx_congr (fun t _ => h2 t)]
  show (if trialIdx m k T r 0 < T then g (trialIdx m k T r 0) else none) = _
  unfold sampleNum
  by_cases ht : trialIdx m k T r 0 < T
  · rw [if_pos ht, if_pos ht]
  · rw [if_neg ht, if_neg ht, dif_neg (lt_irrefl m)]

/-- The sampled edge index is the numeric sample when it is in range, `0` otherwise. -/
theorem sampleEdgeIdx_eq (m T : ℕ) (r : List Bool) :
    sampleEdgeIdx m T r =
      if sampleNum m (Nat.size m) T r < m then sampleNum m (Nat.size m) T r else 0 := by
  unfold sampleEdgeIdx
  rw [sampleIdx_eq]
  split_ifs <;> rfl

/-- The first colour of the sampled pair as a function of the numeric sample (`0`, the first
colour of the default pair, when the sample is out of range). -/
noncomputable def colorA (v : ℕ) : Fin 3 := if h : v < 6 then (pair6Equiv ⟨v, h⟩).1.1 else 0

/-- The second colour of the sampled pair as a function of the numeric sample (`1` when the
sample is out of range). -/
noncomputable def colorB (v : ℕ) : Fin 3 := if h : v < 6 then (pair6Equiv ⟨v, h⟩).1.2 else 1

/-- The first colour of the sampled pair is `colorA` of the numeric sample. -/
theorem sampleColorPair_fst (T : ℕ) (r : List Bool) :
    (sampleColorPair T r).1.1 = colorA (sampleNum 6 3 T r) := by
  unfold sampleColorPair colorA
  rw [sampleIdx_eq]
  split_ifs <;> rfl

/-- The second colour of the sampled pair is `colorB` of the numeric sample. -/
theorem sampleColorPair_snd (T : ℕ) (r : List Bool) :
    (sampleColorPair T r).1.2 = colorB (sampleNum 6 3 T r) := by
  unfold sampleColorPair colorB
  rw [sampleIdx_eq]
  split_ifs <;> rfl

/-! ### The numeric model of the edge list -/

/-- Indexing a product list: `(l₁ ×ˢ l₂)[k] = (l₁[k / |l₂|], l₂[k % |l₂|])`.

**Proof sketch.** Induction on `l₁`: `(a :: l₁) ×ˢ l₂` is `l₂.map (a, ·) ++ l₁ ×ˢ l₂`
(`List.product_cons`); an index `k < |l₂|` falls in the first block (`k / |l₂| = 0`,
`k % |l₂| = k`), a larger one in the tail with index `k - |l₂|`, where `k / |l₂|` and
`k % |l₂|` are those of `k - |l₂|` shifted (`Nat.div_eq_sub_div`, `Nat.mod_eq_sub_mod`). -/
theorem getElem_product {α β : Type*} (l₁ : List α) (l₂ : List β) :
    ∀ (k : ℕ) (hk : k < (l₁ ×ˢ l₂).length) (h₁ : k / l₂.length < l₁.length)
      (h₂ : k % l₂.length < l₂.length),
      (l₁ ×ˢ l₂)[k] = (l₁[k / l₂.length], l₂[k % l₂.length]) := by
  induction l₁ with
  | nil => intro k hk; simp at hk
  | cons a l₁ ih =>
    intro k hk h₁ h₂
    show (List.map (fun b => (a, b)) l₂ ++ l₁ ×ˢ l₂)[k] = _
    by_cases hlt : k < l₂.length
    · rw [List.getElem_append_left (by simpa using hlt), List.getElem_map]
      have hdiv : k / l₂.length = 0 := Nat.div_eq_of_lt hlt
      have hmod : k % l₂.length = k := Nat.mod_eq_of_lt hlt
      simp only [hdiv, hmod, List.getElem_cons_zero]
    · have hle : l₂.length ≤ k := not_lt.1 hlt
      have hpos : 0 < l₂.length := by
        rcases Nat.eq_zero_or_pos l₂.length with h0 | h0
        · exfalso
          rw [List.length_product, h0, Nat.mul_zero] at hk
          exact Nat.not_lt_zero _ hk
        · exact h0
      have hdiv : k / l₂.length = (k - l₂.length) / l₂.length + 1 := Nat.div_eq_sub_div hpos hle
      have hmod : k % l₂.length = (k - l₂.length) % l₂.length := Nat.mod_eq_sub_mod hle
      have hk' : k - l₂.length < (l₁ ×ˢ l₂).length := by
        rw [List.length_product] at hk ⊢
        rw [List.length_cons] at hk
        have : (l₁.length + 1) * l₂.length = l₁.length * l₂.length + l₂.length := by ring
        omega
      have h₁' : (k - l₂.length) / l₂.length < l₁.length := by
        rw [hdiv, List.length_cons] at h₁
        omega
      have h₂' : (k - l₂.length) % l₂.length < l₂.length := hmod ▸ h₂
      have hih := ih (k - l₂.length) hk' h₁' h₂'
      rw [List.getElem_append_right (by simpa using hle)]
      simp only [List.length_map]
      rw [hih]
      simp only [hdiv, hmod, List.getElem_cons_succ]

/-- The square `List.finRange n ×ˢ List.finRange n` is `List.finRange (n * n)` read through
`finProdFinEquiv.symm` (row-major order). -/
theorem finRange_product_eq (n : ℕ) :
    List.finRange n ×ˢ List.finRange n = (List.finRange (n * n)).map finProdFinEquiv.symm := by
  apply List.ext_getElem
  · simp [List.length_product]
  · intro k h₁ h₂
    have hk : k < n * n := by simpa using h₂
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hk
    rw [getElem_product (List.finRange n) (List.finRange n) k h₁
      (by rw [List.length_finRange]; exact (Nat.div_lt_iff_lt_mul hn).2 hk)
      (by rw [List.length_finRange]; exact Nat.mod_lt _ hn)]
    rw [List.getElem_map, List.getElem_finRange, List.getElem_finRange, List.getElem_finRange,
      finProdFinEquiv_symm_apply]
    simp [Fin.divNat, Fin.modNat]

/-- The number of set bits among the first `k` positions of a word (`|E|` of the decoded graph
for `k = n²`). -/
def countBits (x : List Bool) (k : ℕ) : ℕ := ((List.range k).filter fun j => x.getD j false).length

/-- The edge list of the decoded graph is the list of set-bit positions of the adjacency
word, read as pairs through `finProdFinEquiv.symm` (`finRange_product_eq`,
`List.filter_map`). -/
theorem edgeList_eq_map (x : List Bool) :
    edgeList (decGraph x).2 =
      (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
        fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).map
          finProdFinEquiv.symm) := by
  unfold edgeList
  rw [finRange_product_eq, List.filter_map]
  congr 1
  apply List.filter_congr
  intro k _
  show x.getD (finProdFinEquiv (finProdFinEquiv.symm k)) false = x.getD k false
  rw [Equiv.apply_symm_apply]

/-- The filter of `List.finRange M` by a test on values, mapped to values, is the filter of
`List.range M`. -/
theorem map_val_filter_finRange (Q : ℕ → Bool) (M : ℕ) :
    (((List.finRange M).filter fun k : Fin M => Q k).map Fin.val) = (List.range M).filter Q := by
  rw [← List.map_coe_finRange, List.filter_map]
  rfl

/-- `|E|` of the decoded graph is the number of set bits of the adjacency word. -/
theorem edgeCount_eq_countBits (x : List Bool) :
    edgeCount (decGraph x).2 = countBits x ((decGraph x).1 * (decGraph x).1) := by
  show (edgeList (decGraph x).2).length = _
  rw [edgeList_eq_map, List.length_map, countBits, ← map_val_filter_finRange, List.length_map]

/-- The number of set bits is monotone, and strictly so across a set position. -/
theorem countBits_lt_of_lt (x : List Bool) {k k' : ℕ} (hk : k < k') (hQ : x.getD k false = true) :
    countBits x k < countBits x k' := by
  unfold countBits
  obtain ⟨d, rfl⟩ : ∃ d, k' = k + 1 + d := ⟨k' - (k + 1), by omega⟩
  rw [List.range_add, List.filter_append, List.length_append, List.range_succ,
    List.filter_append, List.length_append]
  simp only [List.filter_singleton, hQ, cond_true, List.length_singleton]
  omega

/-- The `e`-th element of the filtered range `(List.range M).filter Q` is a set position `< M`
with exactly `e` set positions before it.

**Proof sketch.** Induction on `M`: `(range (M+1)).filter Q` is `(range M).filter Q ++ [M].filter Q`
(`List.range_succ`, `List.filter_append`); an index below the length of the first part is
covered by the induction hypothesis (`List.getElem_append_left`), otherwise `Q M` holds, the
index equals the length of the first part and the element is `M`. -/
theorem getElem_filter_range_spec (Q : ℕ → Bool) :
    ∀ (M e : ℕ) (he : e < ((List.range M).filter Q).length),
      Q ((List.range M).filter Q)[e] = true ∧ ((List.range M).filter Q)[e] < M ∧
        ((List.range ((List.range M).filter Q)[e]).filter Q).length = e := by
  intro M
  induction M with
  | zero => intro e he; simp at he
  | succ M ih =>
    intro e he
    have hsplit : (List.range (M + 1)).filter Q = (List.range M).filter Q ++ [M].filter Q := by
      rw [List.range_succ, List.filter_append]
    by_cases hlt : e < ((List.range M).filter Q).length
    · have hget : ((List.range (M + 1)).filter Q)[e] = ((List.range M).filter Q)[e] := by
        simp only [hsplit]
        rw [List.getElem_append_left hlt]
      obtain ⟨h1, h2, h3⟩ := ih e hlt
      rw [hget]
      exact ⟨h1, Nat.lt_succ_of_lt h2, h3⟩
    · have hlen : e < ((List.range M).filter Q).length + ([M].filter Q).length := by
        rw [hsplit, List.length_append] at he
        exact he
      have hQM : Q M = true := by
        by_contra hQ
        rw [Bool.not_eq_true] at hQ
        rw [List.filter_singleton] at hlen
        simp [hQ] at hlen
        omega
      have hone : [M].filter Q = [M] := by
        rw [List.filter_singleton]
        simp [hQM]
      have heq : e = ((List.range M).filter Q).length := by
        rw [hone, List.length_singleton] at hlen
        omega
      have hsplit' : (List.range (M + 1)).filter Q = (List.range M).filter Q ++ [M] := by
        rw [hsplit, hone]
      have hget : ((List.range (M + 1)).filter Q)[e] = M := by
        simp only [hsplit']
        rw [List.getElem_append_right (not_lt.1 hlt)]
        simp [heq]
      rw [hget]
      exact ⟨hQM, Nat.lt_succ_self M, heq.symm⟩

/-- The position of the `(e+1)`-th set bit of a word below `n²`: the first `k < n²` that is set
and has exactly `e` set positions before it (`n²` if there is none). -/
noncomputable def edgePos (n : ℕ) (x : List Bool) (e : ℕ) : ℕ :=
  firstIdx (fun k => x.getD k false && decide (countBits x k = e)) (n * n)

/-- The `e`-th set position of a word is `edgePos` (`getElem_filter_range_spec`,
`countBits_lt_of_lt`, `firstIdx_eq_of`). -/
theorem getElem_filter_range_eq_edgePos (n : ℕ) (x : List Bool) (e : ℕ)
    (he : e < ((List.range (n * n)).filter fun j => x.getD j false).length) :
    ((List.range (n * n)).filter fun j => x.getD j false)[e] = edgePos n x e := by
  obtain ⟨h1, h2, h3⟩ := getElem_filter_range_spec (fun j => x.getD j false) (n * n) e he
  set k₀ := ((List.range (n * n)).filter fun j => x.getD j false)[e] with hk₀
  symm
  apply firstIdx_eq_of h2
  · rw [h1, Bool.true_and, decide_eq_true_eq]
    exact h3
  · intro k hk
    by_cases hQ : x.getD k false = true
    · rw [hQ, Bool.true_and, decide_eq_false_iff_not]
      have := countBits_lt_of_lt x hk hQ
      unfold countBits at this ⊢
      omega
    · rw [Bool.not_eq_true] at hQ
      rw [hQ, Bool.false_and]

/-- **The `e`-th edge of the decoded graph is the `(e+1)`-th set bit** of the adjacency word:
its endpoints are `edgePos n x e / n` and `edgePos n x e % n`.

**Proof sketch.** `edgeOf G e` is the `e`-th element of the edge list, which is the filtered
`List.finRange (n²)` read through `finProdFinEquiv.symm` (`edgeList_eq_map`,
`List.getElem_map`); its value is the `e`-th element of the filtered `List.range (n²)`
(`map_val_filter_finRange`, `List.getElem_of_eq`), i.e. `edgePos n x e`
(`getElem_filter_range_eq_edgePos`), and `finProdFinEquiv.symm` splits it into quotient and
remainder (`finProdFinEquiv_symm_apply`). -/
theorem edgeOf_val_eq (x : List Bool) (e : Fin (edgeCount (decGraph x).2)) :
    ((edgeOf (decGraph x).2 e).1 : ℕ) = edgePos (decGraph x).1 x e / (decGraph x).1 ∧
      ((edgeOf (decGraph x).2 e).2 : ℕ) = edgePos (decGraph x).1 x e % (decGraph x).1 := by
  have hlen : (e : ℕ) < (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
      fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).map
        finProdFinEquiv.symm).length := by
    rw [← edgeList_eq_map x]
    exact e.isLt
  have hLe : (e : ℕ) < ((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
      fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).length := by
    simpa using hlen
  have hget : edgeOf (decGraph x).2 e = finProdFinEquiv.symm
      (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
        fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false)[e.val]'hLe) := by
    unfold edgeOf
    rw [List.get_eq_getElem, List.getElem_of_eq (edgeList_eq_map x), List.getElem_map]
  have hval : (((((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
      fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false)[e.val]'hLe) :
        Fin ((decGraph x).1 * (decGraph x).1)) : ℕ) = edgePos (decGraph x).1 x e := by
    have h1 : (e : ℕ) < (((List.finRange ((decGraph x).1 * (decGraph x).1)).filter
        fun k : Fin ((decGraph x).1 * (decGraph x).1) => x.getD k false).map Fin.val).length := by
      simpa using hLe
    have h2 := List.getElem_of_eq
      (map_val_filter_finRange (fun j => x.getD j false) ((decGraph x).1 * (decGraph x).1)) h1
    rw [List.getElem_map] at h2
    rw [h2]
    exact getElem_filter_range_eq_edgePos (decGraph x).1 x e _
  rw [hget, finProdFinEquiv_symm_apply]
  simp only [Fin.divNat, Fin.modNat]
  rw [hval]
  exact ⟨rfl, rfl⟩


/-! ### The numeric form of one attempt -/

/-- The encoding of a message list is the concatenation of the self-delimiting encodings of
its messages (`pairEncode m []` is `dbl m ++ [false, true]`). -/
theorem encodeMsgs_eq_flatMap (l : List (List Bool)) :
    Strategy.encodeMsgs l = l.flatMap fun m => pairEncode m [] := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    rw [Strategy.encodeMsgs_cons, List.flatMap_cons, ih]
    simp [pairEncode, List.append_assoc]

/-- The encoding of a message list given by a function on `Fin n` is the concatenation over
`List.range n` of the encodings of a numeric form of the function. -/
theorem encodeMsgs_ofFn_eq_flatMap {n : ℕ} (F : Fin n → List Bool) (F' : ℕ → List Bool)
    (hF : ∀ i : Fin n, F i = F' i) :
    Strategy.encodeMsgs (List.ofFn F) = (List.range n).flatMap fun i => pairEncode (F' i) [] := by
  rw [encodeMsgs_eq_flatMap, List.ofFn_eq_map, ← List.map_coe_finRange, List.flatMap_map,
    List.flatMap_map]
  congr 1
  funext i
  simp [hF]

/-- The `ℓ`-bit randomness read from position `s` of a tape, as a string: `List.ofFn` of the
`getD` reading is `padL` of the dropped tape. -/
theorem ofFn_getD_eq_padL (blk : List Bool) (s ℓ : ℕ) :
    List.ofFn (fun j : Fin ℓ => blk.getD (s + j) false) = EnsembleLemmas.padL ℓ (blk.drop s) := by
  unfold EnsembleLemmas.padL
  congr 1
  funext j
  simp [padFin, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The vertex count read off an adjacency word. -/
def nV (x : List Bool) : ℕ := Nat.sqrt x.length

/-- The edge count read off an adjacency word: the number of set bits among its first `n²`
positions. -/
def mE (x : List Bool) : ℕ := countBits x (nV x * nV x)

/-- The sampled edge index of an attempt. -/
noncomputable def eIdx (x blk : List Bool) : ℕ := sampleEdgeIdx (mE x) x.length blk

/-- The numeric colour-pair sample of an attempt. -/
noncomputable def vIdx (x blk : List Bool) : ℕ :=
  sampleNum 6 3 x.length (blk.drop ((x.length + 1) ^ 2))

/-- The position of the sampled edge in the adjacency word. -/
noncomputable def kPos (x blk : List Bool) : ℕ := edgePos (nV x) x (eIdx x blk)

/-- The start of the commitment randomness in a coin block. -/
def baseR (x : List Bool) : ℕ := (x.length + 1) ^ 2 + 3 * x.length

/-- The commitment randomness of vertex `i` as a string. -/
noncomputable def rrStr (ℓ : PolyExpr) (x blk : List Bool) (i : ℕ) : List Bool :=
  EnsembleLemmas.padL (ℓ.eval (nV x)) (blk.drop (baseR x + i * ℓ.eval (nV x)))

/-- The simulator's colour of vertex `i` in numeric form: the sampled pair at the endpoints of
the sampled edge, `0` elsewhere. -/
noncomputable def colorNum (x blk : List Bool) (i : ℕ) : Fin 3 :=
  if i = kPos x blk / nV x then colorA (vIdx x blk)
  else if i = kPos x blk % nV x then colorB (vIdx x blk) else 0

/-- The encoded commitment of vertex `i` to the colour `c i`. -/
noncomputable def chunk (Com : List Bool → List Bool) (ℓ : PolyExpr) (x blk : List Bool)
    (c : ℕ → Fin 3) (i : ℕ) : List Bool :=
  pairEncode (Com (pairEncode (EnsembleLemmas.padL (nV x) (encColor (c i))) (rrStr ℓ x blk i))) []

/-- The commitment message to the colouring `c` in numeric form. -/
noncomputable def comStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (x blk : List Bool)
    (c : ℕ → Fin 3) : List Bool :=
  (List.range (nV x)).flatMap (chunk Com ℓ x blk c)

/-- The tape handed to `V'`. -/
def rVStr (ℓ : PolyExpr) (x blk : List Bool) : List Bool :=
  blk.drop (baseR x + x.length * ℓ.eval x.length)

/-- The opening message in numeric form. -/
noncomputable def opnStr (ℓ : PolyExpr) (x blk : List Bool) : List Bool :=
  pairEncode
    (pairEncode (encColor (colorNum x blk (kPos x blk / nV x))) (rrStr ℓ x blk (kPos x blk / nV x)))
    (pairEncode (encColor (colorNum x blk (kPos x blk % nV x))) (rrStr ℓ x blk (kPos x blk % nV x)))

/-- One attempt in numeric form: if the graph has no edge, the view with the all-zero
commitments and the empty opening; otherwise the view with the simulated commitments and the
opening of the sampled edge if `V'` names that edge, `none` otherwise. -/
noncomputable def attemptNum (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : Option (List Bool) :=
  if mE x = 0 then
    some (View.encode ⟨x, z, rVStr ℓ x blk, [comStr Com ℓ x blk (fun _ => 0), []]⟩)
  else if (V'.next x z (rVStr ℓ x blk) [comStr Com ℓ x blk (colorNum x blk)]).length % mE x =
      eIdx x blk then
    some (View.encode ⟨x, z, rVStr ℓ x blk, [comStr Com ℓ x blk (colorNum x blk), opnStr ℓ x blk]⟩)
  else none

/-- The commitment message of the typed attempt is the numeric commitment message. -/
theorem colCommit_eq_comStr (Com : List Bool → List Bool) (ℓ : PolyExpr) (x blk : List Bool)
    (c' : Fin (nV x) → Fin 3) (c : ℕ → Fin 3) (hc : ∀ i : Fin (nV x), c' i = c i) :
    colCommit Com (nV x) (ℓ.eval (nV x)) c'
        (fun i j => blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false) =
      comStr Com ℓ x blk c := by
  unfold colCommit multiCom comStr
  apply encodeMsgs_ofFn_eq_flatMap
  intro i
  simp only [rrStr, hc i, ← ofFn_getD_eq_padL]
  rfl

/-- **One attempt of the string simulator is its numeric form** (the content of the machine's
correctness).

**Proof sketch.** The vertex count is `nV x` by definition of `decGraph`, the edge count is
`mE x` (`edgeCount_eq_countBits`). If `E = ∅` the attempt takes the `none` branch of `edgeAt`
(`edgeAt_eq_none_iff`) and its commitments are `comStr` to the all-zero colouring
(`colCommit_eq_comStr`). Otherwise the sampled index is in range (`sampleEdgeIdx_lt`), `edgeAt`
is the `e'`-th edge (`edgeAt_eq_some_edgeOf`), whose endpoints are `kPos / nV` and `kPos % nV`
(`edgeOf_val_eq`); the typed colours are `colorNum` (`sampleColorPair_fst/snd`), the
commitments are `comStr` and the opening is `opnStr`. -/
theorem attemptStr_eq_attemptNum (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
    (x z blk : List Bool) : attemptStr Com ℓ V' x z blk = attemptNum Com ℓ V' x z blk := by
  have hm : edgeCount (decGraph x).2 = mE x := edgeCount_eq_countBits x
  have hn : (decGraph x).1 = nV x := rfl
  unfold attemptStr attemptNum
  simp only []
  by_cases hm0 : mE x = 0
  · rw [if_pos hm0]
    have hnone : edgeAt (decGraph x).2 (sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk) =
        none := (edgeAt_eq_none_iff _ _).2 (hm.trans hm0)
    rw [hnone]
    show some (View.encode ⟨x, z,
      blk.drop ((x.length + 1) ^ 2 + 3 * x.length + x.length * ℓ.eval x.length),
      [colCommit Com (nV x) (ℓ.eval (nV x)) (fun _ => 0)
        (fun i j => blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false),
        []]⟩) = _
    rw [colCommit_eq_comStr Com ℓ x blk (fun _ => 0) (fun _ => 0) (fun _ => rfl)]
    rfl
  · rw [if_neg hm0]
    have hmpos : 0 < edgeCount (decGraph x).2 := by rw [hm]; exact Nat.pos_of_ne_zero hm0
    have he : sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk < edgeCount (decGraph x).2 :=
      sampleEdgeIdx_lt hmpos _ _
    set ef : Fin (edgeCount (decGraph x).2) := ⟨_, he⟩ with hef
    have hsome : edgeAt (decGraph x).2 (sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk) =
        some (edgeOf (decGraph x).2 ef) := edgeAt_eq_some_edgeOf (decGraph x).2 ef
    rw [hsome]
    obtain ⟨hp1, hp2⟩ := edgeOf_val_eq x ef
    have heI : (ef : ℕ) = eIdx x blk := by
      show sampleEdgeIdx (edgeCount (decGraph x).2) x.length blk = eIdx x blk
      rw [hm]
      rfl
    have hkPos : edgePos (decGraph x).1 x ef = kPos x blk := by
      rw [heI]
      rfl
    rw [hkPos] at hp1 hp2
    have hcol : ∀ i : Fin (nV x),
        simColors (edgeOf (decGraph x).2 ef) (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))) i =
          colorNum x blk i := by
      intro i
      unfold simColors colorNum
      simp only [sampleColorPair_fst, sampleColorPair_snd, Fin.ext_iff, hp1, hp2]
      rfl
    have hcom := colCommit_eq_comStr Com ℓ x blk _ _ hcol
    have hopn : colOpen
        (simColors (edgeOf (decGraph x).2 ef) (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
        (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
          blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false)
        (edgeOf (decGraph x).2 ef) = opnStr ℓ x blk := by
      unfold colOpen opnStr
      simp only [hcol]
      rw [hp1, hp2]
      unfold rrStr
      rw [← ofFn_getD_eq_padL, ← ofFn_getD_eq_padL]
      rfl
    show (if edgeIdxOfMsg (edgeCount (decGraph x).2)
        (V'.next x z (blk.drop ((x.length + 1) ^ 2 + 3 * x.length + x.length * ℓ.eval x.length))
          [colCommit Com (nV x) (ℓ.eval (nV x))
            (simColors (edgeOf (decGraph x).2 ef)
              (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
            (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
              blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false)])
          = (ef : ℕ) then
        some (View.encode ⟨x, z,
          blk.drop ((x.length + 1) ^ 2 + 3 * x.length + x.length * ℓ.eval x.length),
          [colCommit Com (nV x) (ℓ.eval (nV x))
            (simColors (edgeOf (decGraph x).2 ef)
              (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
            (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
              blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false),
           colOpen (simColors (edgeOf (decGraph x).2 ef)
              (sampleColorPair x.length (blk.drop ((x.length + 1) ^ 2))))
            (fun (i : Fin (nV x)) (j : Fin (ℓ.eval (nV x))) =>
              blk.getD ((x.length + 1) ^ 2 + 3 * x.length + i * ℓ.eval (nV x) + j) false)
            (edgeOf (decGraph x).2 ef)]⟩)
      else none) = _
    simp only [hcom, hopn, heI, hm]
    rfl

end TCSlib.Cryptography.ColSimMachine
