/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.DetModMath
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassP.BinaryArith.ModPow

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The determinant over `ZMod p` in polynomial time

Infrastructure for [AB09 §7.2.4] (Lovász's test evaluates a determinant over a prime field);
not itself a result of the book. Input: `⟨p, rows⟩`, `p` in binary and the matrix as the list
(`Complexity.BinArith.encWords`) of its rows, each the list of its entries `Nat.bits x`
(`Complexity.BinArith.encMat`). Output: `Nat.bits (det M).val` for the matrix `M` over
`ZMod p`, by Gaussian elimination: with a nonzero head in the first row, eliminate the first
column (pivot inverse `a^(p-2) mod p`, Fermat) and drop to the Schur complement; with a zero
head, rotate the first row to the bottom; after a full round of rotations the first column is
zero and the determinant is `0`.

## Main definitions

* `Complexity.BinArith.encRow`, `Complexity.BinArith.encMat` — the input encoding.
* `Complexity.BinArith.detStep` — one elimination round on `(rows, d, m, rc)`; `detWStep` is its
  word-level form.
* `Complexity.BinArith.detModAlg` — the algorithm.

## Main results

* `Complexity.BinArith.polyTimeComputable_detModAlg` — the algorithm is polynomial-time.
* `Complexity.BinArith.detModAlg_pairEncode` — for a prime `p` and a square matrix it outputs
  `Nat.bits (det (matOfRows p n rows)).val`.

## Divergences

* Correctness is stated for prime `p` and square row lists (every row of length `n`, the
  number of rows); entries are arbitrary naturals, read modulo `p`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.2.4.)
-/

namespace Complexity

namespace BinArith

open Turing LogProg

/-! ### Encodings and slots -/

/-- A row of numbers, as the list of their binary words. -/
def encRow (r : List ℕ) : List Bool := encWords (r.map Nat.bits)

/-- A matrix, as the list of its encoded rows. -/
def encMat (R : List (List ℕ)) : List Bool := encWords (R.map encRow)

/-- The state of the elimination loop: rows, accumulated factor `d`, size `m`, rotations `rc`. -/
abbrev DState := List (List ℕ) × ℕ × ℕ × ℕ

/-- The word of a state: `⟨p, ⟨rows, ⟨d, ⟨1^m, 1^rc⟩⟩⟩⟩`. -/
def encState (p : ℕ) : DState → List Bool
  | (R, d, m, rc) => pairEncode (Nat.bits p) (pairEncode (encMat R) (pairEncode (Nat.bits d)
    (pairEncode (List.replicate m true) (List.replicate rc true))))

/-- The head entry word of an encoded row. -/
@[simp] theorem pairFstD_encRow (r : List ℕ) : pairFstD (encRow r) = Nat.bits (r.headD 0) := by
  cases r <;> simp [encRow, Nat.zero_bits, pairFstD_nil]

/-- The tail of an encoded row. -/
@[simp] theorem pairSndD_encRow (r : List ℕ) : pairSndD (encRow r) = encRow r.tail := by
  cases r
  · rfl
  · simp [encRow]

/-- Reading an encoded row. -/
@[simp] theorem decWords_encRow (r : List ℕ) : decWords (encRow r) = r.map Nat.bits := by
  simp [encRow]

/-- Reading an encoded matrix. -/
@[simp] theorem decWords_encMat (R : List (List ℕ)) : decWords (encMat R) = R.map encRow := by
  simp [encMat]

/-- A pair is never the empty word. -/
@[simp] theorem isNilB_pairEncode (a b : List Bool) : isNilB (pairEncode a b) = false := by
  simp [isNilB, pairEncode]

/-- The empty matrix is the empty word, and only it. -/
theorem encMat_eq_nil_iff (R : List (List ℕ)) : encMat R = [] ↔ R = [] := by
  cases R <;> simp [encMat, pairEncode]

/-- The first row of an encoded matrix. -/
@[simp] theorem pairFstD_encMat_cons (r : List ℕ) (R : List (List ℕ)) :
    pairFstD (encMat (r :: R)) = encRow r := by simp [encMat]

/-- The remaining rows of an encoded matrix. -/
@[simp] theorem pairSndD_encMat_cons (r : List ℕ) (R : List (List ℕ)) :
    pairSndD (encMat (r :: R)) = encMat R := by simp [encMat]

/-! ### One elimination round -/

/-- The entry update on `⟨⟨p, f⟩, ⟨r, y⟩⟩`: `(r + p - (f·y mod p)) mod p`. -/
def entryW (w : List Bool) : List Bool :=
  mod (pairEncode (sub (pairEncode
      (add (pairEncode (pairFstD (pairSndD w)) (pairFstD (pairFstD w))))
      (mod (pairEncode (mul (pairEncode (pairSndD (pairFstD w)) (pairSndD (pairSndD w))))
        (pairFstD (pairFstD w))))))
    (pairFstD (pairFstD w)))

/-- `entryW` on encoded numbers. -/
theorem entryW_eq (p f r y : ℕ) :
    entryW (pairEncode (pairEncode (Nat.bits p) (Nat.bits f))
      (pairEncode (Nat.bits r) (Nat.bits y)))
      = Nat.bits ((r + p - f * y % p) % p) := by
  simp [entryW]

/-- The row update on `⟨⟨p, ⟨inv, pivot tail⟩⟩, row⟩`: zip the row's tail with the pivot's tail
under `entryW`, with factor `f = row[0]·inv mod p`. -/
def rowW (w : List Bool) : List Bool :=
  zipWithW entryW (pairEncode
    (pairEncode (pairFstD (pairFstD w)) (mod (pairEncode (mul (pairEncode
      (pairFstD (pairSndD w)) (pairFstD (pairSndD (pairFstD w))))) (pairFstD (pairFstD w)))))
    (pairEncode (pairSndD (pairSndD w)) (pairSndD (pairSndD (pairFstD w)))))

/-- `rowW` computes `elimRow`. -/
theorem rowW_eq (p inv : ℕ) (piv row : List ℕ) :
    rowW (pairEncode (pairEncode (Nat.bits p) (pairEncode (Nat.bits inv) (encRow piv.tail)))
      (encRow row)) = encRow (elimRow p inv piv row) := by
  simp only [rowW, pairFstD_pairEncode, pairSndD_pairEncode, pairFstD_encRow, pairSndD_encRow,
    mod, mul, bitsVal_bits, zipWithW_pairEncode, decWords_encRow, List.zipWith_map, entryW_eq]
  simp [encRow, elimRow, List.map_zipWith]

/-- The parity test `|w|` even is polynomial-time (the last running parity of a transducer). -/
theorem polyTimeComputable_evenLength :
    PolyTimeComputable (fun w : List Bool => [decide (w.length % 2 = 0)]) := by
  have hlast : ∀ (w : List Bool) (s : Bool),
      (transduce (fun s _ => !s) (fun s _ => some (!s)) s w).getLastD s =
        (s ^^ decide (w.length % 2 = 1)) := by
    intro w
    induction w with
    | nil => intro s; simp [transduce]
    | cons b w ih =>
      intro s
      simp only [transduce, Option.toList_some, List.singleton_append, List.getLastD_cons, ih,
        List.length_cons]
      cases s <;> rcases Nat.mod_two_eq_zero_or_one w.length with h | h <;> simp [h] <;> omega
  convert polyTimeComputable_not (polyTimeComputable_lastBit.comp
    (polyTimeComputable_transduce (σ := Bool) (fun s _ => !s) (fun s _ => some (!s)) false))
    using 1
  funext w
  simp only [hlast, Bool.false_xor, List.cons.injEq, and_true]
  rcases Nat.mod_two_eq_zero_or_one w.length with h | h <;> simp [h]

/-- One elimination round on `(rows, d, m, rc)` over `ZMod p` (fixed when `p < 2` or there are
no rows): after `m` rotations (`rc ≥ m`) the first column is zero, so finish with `d = 0`; with
a zero head, rotate the first row to the bottom (sign `(-1)^(m-1)`); else eliminate with the
first row as pivot, multiplying `d` by the pivot. -/
def detStep (p : ℕ) (s : DState) : DState :=
  if p < 2 then s else
  match s with
  | ([], _, _, _) => s
  | (r₀ :: rs, d, m, rc) =>
    if m ≤ rc then ([], 0, 0, 0)
    else if r₀.headD 0 = 0 then (rs ++ [r₀], if m % 2 = 0 then d * (p - 1) % p else d, m, rc + 1)
    else (rs.map (elimRow p (r₀.headD 0 ^ (p - 2) % p) r₀), d * r₀.headD 0 % p, m - 1, 0)

/-- The modulus slot. -/
def slP (S : List Bool) : List Bool := pairFstD S
/-- The rows slot. -/
def slR (S : List Bool) : List Bool := pairFstD (pairSndD S)
/-- The factor slot `d`. -/
def slD (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD S))
/-- The size slot `1^m`. -/
def slM (S : List Bool) : List Bool := pairFstD (pairSndD (pairSndD (pairSndD S)))
/-- The rotation slot `1^rc`. -/
def slC (S : List Bool) : List Bool := pairSndD (pairSndD (pairSndD (pairSndD S)))

/-- The word-level elimination round on `⟨p, ⟨rows, ⟨d, ⟨1^m, 1^rc⟩⟩⟩⟩`. -/
def detWStep (S : List Bool) : List Bool :=
  if decide (bitsVal (slP S) < 2) || isNilB (slR S) then S
  else if decide ((slM S).length ≤ (slC S).length) then
    pairEncode (slP S) (pairEncode [] (pairEncode [] (pairEncode [] [])))
  else if decide (bitsVal (pairFstD (pairFstD (slR S))) = 0) then
    pairEncode (slP S) (pairEncode (pairSndD (slR S) ++ pairEncode (pairFstD (slR S)) [])
      (pairEncode (if decide ((slM S).length % 2 = 0) then
          mod (pairEncode (mul (pairEncode (slD S) (sub (pairEncode (slP S) [true])))) (slP S))
        else slD S) (pairEncode (slM S) (true :: slC S))))
  else
    pairEncode (slP S) (pairEncode
      (mapW rowW (pairEncode (pairEncode (slP S) (pairEncode
        (powMod (pairEncode (pairFstD (pairFstD (slR S)))
          (pairEncode (sub (pairEncode (slP S) (Nat.bits 2))) (slP S))))
        (pairSndD (pairFstD (slR S))))) (pairSndD (slR S))))
      (pairEncode (mod (pairEncode (mul (pairEncode (slD S) (pairFstD (pairFstD (slR S)))))
        (slP S))) (pairEncode ((slM S).drop 1) [])))

/-- **The word-level round implements `detStep`.**

**Proof sketch.** Case on `p < 2`, empty rows, `m ≤ rc` and the head of the first row; in each
case the slot projections of `encState` reduce, the rotation uses
`encWords_append_singleton`, and the elimination uses `mapW_pairEncode` with `rowW_eq` and
the arithmetic `_pairEncode` lemmas. -/
theorem detWStep_encState (p : ℕ) (s : DState) :
    detWStep (encState p s) = encState p (detStep p s) := by
  obtain ⟨R, d, m, rc⟩ := s
  by_cases hp : p < 2
  · simp [detWStep, detStep, encState, slP, bitsVal_bits, hp]
  cases R with
  | nil => simp [detWStep, detStep, encState, slP, slR, bitsVal_bits, hp, isNilB, encMat]
  | cons r₀ rs =>
    have hp0 : p ≠ 0 := by omega
    have hnil : isNilB (encMat (r₀ :: rs)) = false := by
      simp [isNilB, encMat_eq_nil_iff]
    by_cases hmc : m ≤ rc
    · simp [detWStep, detStep, encState, slP, slR, slM, slC, bitsVal_bits, hp, hmc, encMat,
        Nat.zero_bits]
    by_cases h0 : r₀.headD 0 = 0
    · simp only [detWStep, detStep, encState, slP, slR, slD, slM, slC, pairFstD_pairEncode,
        pairSndD_pairEncode, bitsVal_bits, hp, hnil, decide_false, Bool.or_false,
        Bool.false_eq_true, if_false, List.length_replicate, hmc, pairFstD_encMat_cons,
        pairFstD_encRow, h0, decide_true, if_true, pairSndD_encMat_cons]
      refine congrArg _ (congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_))
      · simp [encMat, encWords_append_singleton]
      · split_ifs <;> simp_all [mod, mul, sub, bitsVal_bits, bitsVal]
      · rfl
    · simp only [detWStep, detStep, encState, slP, slR, slD, slM, slC, pairFstD_pairEncode,
        pairSndD_pairEncode, bitsVal_bits, hp, hnil, decide_false, Bool.or_false,
        Bool.false_eq_true, if_false, List.length_replicate, hmc, pairFstD_encMat_cons,
        pairFstD_encRow, h0, pairSndD_encMat_cons, pairSndD_encRow]
      refine congrArg _ (congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_))
      · rw [show Nat.bits 2 = Nat.bits 2 from rfl, sub_pairEncode, powMod_pairEncode _ _ _ hp0,
          mapW_pairEncode, decWords_encMat, List.map_map]
        simp only [encMat, List.map_map]
        congr 1
        refine List.map_congr_left (fun r _ => ?_)
        exact rowW_eq p _ r₀ r
      · simp [mod, mul, bitsVal_bits]
      · simp [List.drop_replicate]

/-- The entry update is polynomial-time. -/
theorem polyTimeComputable_entryW : PolyTimeComputable entryW := by
  have hp : PolyTimeComputable (fun w => pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hf : PolyTimeComputable (fun w => pairSndD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  exact polyTimeComputable_mod.comp ((polyTimeComputable_sub.comp
    ((polyTimeComputable_add.comp (polyTimeComputable_slot2.pairEncode hp)).pairEncode
      (polyTimeComputable_mod.comp ((polyTimeComputable_mul.comp
        (hf.pairEncode polyTimeComputable_slot3)).pairEncode hp)))).pairEncode hp)

/-- The row update is polynomial-time. -/
theorem polyTimeComputable_rowW : PolyTimeComputable rowW := by
  have hq := polyTimeComputable_pairFstD
  have hp : PolyTimeComputable (fun w => pairFstD (pairFstD w)) :=
    polyTimeComputable_pairFstD.comp hq
  have hinv : PolyTimeComputable (fun w => pairFstD (pairSndD (pairFstD w))) :=
    polyTimeComputable_slot2.comp hq
  have hpt : PolyTimeComputable (fun w => pairSndD (pairSndD (pairFstD w))) :=
    polyTimeComputable_slot3.comp hq
  exact (polyTimeComputable_zipWithW polyTimeComputable_entryW).comp
    ((hp.pairEncode (polyTimeComputable_mod.comp ((polyTimeComputable_mul.comp
      (polyTimeComputable_slot2.pairEncode hinv)).pairEncode hp))).pairEncode
      (polyTimeComputable_slot3.pairEncode hpt))

/-- `detWStep` is polynomial-time.

**Proof sketch.** The five slots of the state are projections; the tests `p < 2`, "no rows",
`m ≤ rc` and "zero pivot", the factor update `d · x mod p`, and the pivot inverse
`x^{p-2} mod p` (`powMod`) compose from the arithmetic kit; each branch of `detWStep` is then a
pairing of these, the elimination branch with the map loop `mapW rowW`, and the branches are
joined by `polyTimeComputable_ite`. -/
theorem polyTimeComputable_detWStep : PolyTimeComputable detWStep := by
  have hP : PolyTimeComputable slP := polyTimeComputable_pairFstD
  have hR : PolyTimeComputable slR := polyTimeComputable_slot2
  have hD : PolyTimeComputable slD := polyTimeComputable_pairFstD.comp polyTimeComputable_slot3
  have hM : PolyTimeComputable slM :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_slot3)
  have hC : PolyTimeComputable slC := polyTimeComputable_slot4.comp polyTimeComputable_pairSndD
  have hR0 : PolyTimeComputable (fun S => pairFstD (slR S)) := polyTimeComputable_pairFstD.comp hR
  have ha : PolyTimeComputable (fun S => pairFstD (pairFstD (slR S))) :=
    polyTimeComputable_pairFstD.comp hR0
  have hRs : PolyTimeComputable (fun S => pairSndD (slR S)) := polyTimeComputable_pairSndD.comp hR
  have hmodmul : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → PolyTimeComputable g →
      PolyTimeComputable (fun S => mod (pairEncode (mul (pairEncode (f S) (g S))) (slP S))) :=
    fun hf hg => polyTimeComputable_mod.comp
      ((polyTimeComputable_mul.comp (hf.pairEncode hg)).pairEncode hP)
  have hsmall : PolyTimeComputable (fun S => [decide (bitsVal (slP S) < 2)]) := by
    convert polyTimeComputable_lt.comp (hP.pairEncode (polyTimeComputable_const (Nat.bits 2)))
      using 1
    funext S; simp [lt, bitsVal_bits]
  have hmc : PolyTimeComputable (fun S => [decide ((slM S).length ≤ (slC S).length)]) := by
    convert polyTimeComputable_lenLe.comp (hC.pairEncode hM) using 1
    funext S; simp
  have hinv : PolyTimeComputable (fun S => powMod (pairEncode (pairFstD (pairFstD (slR S)))
      (pairEncode (sub (pairEncode (slP S) (Nat.bits 2))) (slP S)))) :=
    polyTimeComputable_powMod.comp (ha.pairEncode ((polyTimeComputable_sub.comp
      (hP.pairEncode (polyTimeComputable_const _))).pairEncode hP))
  unfold detWStep
  refine polyTimeComputable_ite (polyTimeComputable_or hsmall
    (polyTimeComputable_isNil.comp hR)) polyTimeComputable_id ?_
  refine polyTimeComputable_ite hmc (hP.pairEncode (polyTimeComputable_const _)) ?_
  refine polyTimeComputable_ite (polyTimeComputable_isZero.comp ha) ?_ ?_
  · exact hP.pairEncode ((hRs.append (hR0.pairEncode (polyTimeComputable_const []))).pairEncode
      ((polyTimeComputable_ite (polyTimeComputable_evenLength.comp hM)
        (hmodmul hD (polyTimeComputable_sub.comp (hP.pairEncode
          (polyTimeComputable_const [true])))) hD).pairEncode
        (hM.pairEncode (polyTimeComputable_cons (polyTimeComputable_const [true]) hC))))
  · exact hP.pairEncode (((polyTimeComputable_mapW polyTimeComputable_rowW).comp
      ((hP.pairEncode (hinv.pairEncode (polyTimeComputable_pairSndD.comp hR0))).pairEncode
        hRs)).pairEncode ((hmodmul hD ha).pairEncode ((polyTimeComputable_tail.comp hM).pairEncode
          (polyTimeComputable_const []))))

/-! ### Initialization and the loop -/

/-- Entry reduction on `⟨p, e⟩`: `e mod p`. -/
def entryModW (w : List Bool) : List Bool := mod (pairEncode (pairSndD w) (pairFstD w))

/-- Row reduction on `⟨p, row⟩`: every entry mod `p`. -/
def rowModW (w : List Bool) : List Bool := mapW entryModW w

/-- The rows read from `z = ⟨p, rows⟩`, entries reduced modulo `p`. -/
def initRows (z : List Bool) : List (List ℕ) :=
  (decWords (pairSndD z)).map
    (fun rw => (decWords rw).map (fun e => bitsVal e % bitsVal (pairFstD z)))

/-- The initial word of the loop: `⟨p, ⟨rows mod p, ⟨1, ⟨1^m, []⟩⟩⟩⟩`. -/
def initW (z : List Bool) : List Bool :=
  pairEncode (Nat.bits (bitsVal (pairFstD z))) (pairEncode
    (mapW rowModW (pairEncode (Nat.bits (bitsVal (pairFstD z))) (pairSndD z)))
    (pairEncode [true] (pairEncode (countW (pairSndD z)) [])))

/-- The initial word encodes the initial state. -/
theorem initW_eq (z : List Bool) :
    initW z = encState (bitsVal (pairFstD z)) (initRows z, 1, (initRows z).length, 0) := by
  simp only [initW, encState, mapW_pairEncode, rowModW, countW_eq, initRows, List.length_map,
    Nat.one_bits, List.replicate_zero, encMat, List.map_map]
  congr 3
  refine List.map_congr_left (fun rw _ => ?_)
  simp [encRow, entryModW, mod, bitsVal_bits, List.map_map, Function.comp_def]

/-- The determinant algorithm on `⟨p, rows⟩`: `[]` for `p < 2`, else the factor slot after
`(|z| + 1)²` elimination rounds. -/
def detModAlg (z : List Bool) : List Bool :=
  if decide (bitsVal (pairFstD z) < 2) then []
  else slD (detWStep^[1 * (z.length + 1) ^ 2] (initW z))

/-- The rounds commute with the encoding. -/
theorem iterate_detWStep_encState (p : ℕ) (s : DState) (n : ℕ) :
    detWStep^[n] (encState p s) = encState p ((detStep p)^[n] s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      detWStep_encState, ih]

/-! ### Length bounds -/

/-- The length invariant on input `z` (with `p = bitsVal (fst z)`, `K = |z|`): at most `K` rows
of at most `K` entries, entries and `d` below `p + 2^K + 2`, `m` the number of rows, `rc ≤ m`. -/
def LInv (Q K : ℕ) : DState → Prop
  | (R, d, m, rc) => R.length = m ∧ R.length ≤ K ∧ (∀ r ∈ R, r.length ≤ K) ∧
    (∀ r ∈ R, ∀ x ∈ r, x < Q) ∧ d < Q ∧ rc ≤ m

/-- Entries of a zipped list of residues are residues. -/
theorem lt_of_mem_zipWith {p : ℕ} (f : ℕ → ℕ → ℕ) (hf : ∀ a b, f a b < p) :
    ∀ (l₁ l₂ : List ℕ), ∀ x ∈ List.zipWith f l₁ l₂, x < p := by
  intro l₁
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    intro l₂ x hx
    cases l₂ with
    | nil => simp at hx
    | cons b l₂ =>
      simp only [List.zipWith_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hf a b
      · exact ih l₂ x hx

/-- Entries of an eliminated row are residues mod `p`. -/
theorem lt_of_mem_elimRow {p : ℕ} (hp : 0 < p) (inv : ℕ) (piv row : List ℕ) :
    ∀ x ∈ elimRow p inv piv row, x < p :=
  lt_of_mem_zipWith _ (fun _ _ => Nat.mod_lt _ hp) _ _

/-- The length of an eliminated row. -/
theorem length_elimRow (p inv : ℕ) (piv row : List ℕ) :
    (elimRow p inv piv row).length = min (row.length - 1) (piv.length - 1) := by
  simp [elimRow]

/-- The round preserves the length invariant.

**Proof sketch.** Cases as in `detStep`. If `p < 2`, there are no rows or `m ≤ rc`, the state
is kept or only its counters change. A zero pivot moves the first row to the end (lengths
unchanged; the new factor is a residue below `p ≤ Q`). Otherwise every row becomes `elimRow`,
one entry shorter (`length_elimRow`) with entries below `p` (`lt_of_mem_elimRow`). -/
theorem lInv_step (p Q K : ℕ) (hpQ : p ≤ Q) {s : DState} (h : LInv Q K s) :
    LInv Q K (detStep p s) := by
  obtain ⟨R, d, m, rc⟩ := s
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  by_cases hp : p < 2
  · simpa [detStep, hp] using ⟨h1, h2, h3, h4, h5, h6⟩
  cases R with
  | nil => simpa [detStep, hp] using ⟨h1, h2, h3, h4, h5, h6⟩
  | cons r₀ rs =>
    simp only [List.length_cons] at h1 h2
    have hp0 : 0 < p := by omega
    by_cases hmc : m ≤ rc
    · simp only [detStep, hp, hmc, if_true, if_false]
      exact ⟨rfl, by simp, by simp, by simp, by omega, le_rfl⟩
    by_cases h0 : r₀.headD 0 = 0
    · simp only [detStep, hp, hmc, h0, if_false, if_true]
      refine ⟨by simp; omega, by simp; omega, fun r hr => h3 r (by simp at hr ⊢; tauto),
        fun r hr => h4 r (by simp at hr ⊢; tauto), ?_, by omega⟩
      split_ifs
      · have := Nat.mod_lt (d * (p - 1)) hp0; omega
      · exact h5
    · simp only [detStep, hp, hmc, h0, if_false]
      refine ⟨by simp; omega, by simp; omega, fun r hr => ?_, fun r hr x hx => ?_, ?_, by omega⟩
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
        rw [length_elimRow]
        have := h3 r' (by simp [hr'])
        omega
      · obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr
        have := lt_of_mem_elimRow hp0 _ _ _ x hx
        omega
      · have := Nat.mod_lt (d * r₀.headD 0) hp0; omega

/-- A number below `p + 2^K + 2`, `p < 2^K`, has a binary word of at most `K + 2` letters. -/
theorem length_bits_le_of_lt_Q {p K x : ℕ} (hp : p < 2 ^ K) (hx : x < p + 2 ^ K + 2) :
    (Nat.bits x).length ≤ K + 2 :=
  length_bits_le (by
    have := Nat.one_le_two_pow (n := K)
    rw [pow_add]; omega)

/-- A state satisfying the length invariant has a word of length at most `64(|z| + 1)³`.

**Proof sketch.** Entries have at most `|z| + 2` bits (`length_bits_le_of_lt_Q`), rows at most
`|z|` entries and matrices at most `|z|` rows, so `length_encWords_le` bounds a row by
`|z|(2|z| + 6)` and the matrix by `|z|(2|z|(2|z| + 6) + 2)`; the counters add lower-order
terms. -/
theorem length_encState_le (z : List Bool) {s : DState}
    (h : LInv (bitsVal (pairFstD z) + 2 ^ z.length + 2) z.length s) :
    (encState (bitsVal (pairFstD z)) s).length ≤ 64 * (z.length + 1) ^ 3 := by
  obtain ⟨R, d, m, rc⟩ := s
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  set K := z.length
  have hpK : bitsVal (pairFstD z) < 2 ^ K := (bitsVal_lt_two_pow _).trans_le
    (Nat.pow_le_pow_right (by norm_num) (length_pairFstD_le z))
  have hbp : (Nat.bits (bitsVal (pairFstD z))).length ≤ K :=
    (length_bits_bitsVal_le _).trans (length_pairFstD_le z)
  have hrow : ∀ r ∈ R, (encRow r).length ≤ K * (2 * K + 6) := by
    intro r hr
    have := length_encWords_le (r.map Nat.bits) (K + 2) (fun w hw => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hw
      exact length_bits_le_of_lt_Q hpK (h4 r hr x hx))
    simp only [List.length_map] at this
    have := h3 r hr
    unfold encRow
    nlinarith
  have hmat : (encMat R).length ≤ K * (2 * (K * (2 * K + 6)) + 2) := by
    have := length_encWords_le (R.map encRow) (K * (2 * K + 6)) (fun w hw => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hw
      exact hrow r hr)
    simp only [List.length_map] at this
    unfold encMat
    exact this.trans (Nat.mul_le_mul_right _ h2)
  have hbd := length_bits_le_of_lt_Q hpK h5
  simp only [encState, length_pairEncode, List.length_replicate]
  nlinarith

/-! ### Correctness -/

/-- The correctness invariant over `ZMod p` with target `D₀`: square rows of residues, `d < p`,
the last `rc` rows start with `0`, and `det(rows) · d = D₀`. -/
def CInv (p : ℕ) (D₀ : ZMod p) : DState → Prop
  | (R, d, m, rc) => R.length = m ∧ (∀ r ∈ R, r.length = m) ∧ (∀ r ∈ R, ∀ x ∈ r, x < p) ∧
    d < p ∧ rc ≤ m ∧ (∀ i, m - rc ≤ i → i < m → (R.getD i []).headD 0 = 0) ∧
    (matOfRows p m R).det * (d : ZMod p) = D₀

/-- The potential `m(m + 2) - rc` of the elimination loop. -/
def dMeasure : DState → ℕ
  | (_, _, m, rc) => m * (m + 2) - rc

/-- **The elimination round preserves the correctness invariant**, lowers a positive
potential, and fixes potential `0`.

**Proof sketch.** With `m ≤ rc` every row starts with `0`, so `det = 0`
(`det_matOfRows_eq_zero`) and finishing with `d = 0` keeps `det · d = D₀`. A rotation
multiplies `det` by `(-1)^(m-1)` (`det_matOfRows_rotate`), which the factor `p - 1 ≡ -1`
cancels when `m` is even. An elimination with pivot `a ≠ 0` gives `det = a · det'`
(`det_matOfRows_elim`, inverse `a^(p-2)` by Fermat), absorbed into `d · a`. -/
theorem cInv_step {p : ℕ} [Fact p.Prime] {D₀ : ZMod p} {s : DState} (h : CInv p D₀ s) :
    CInv p D₀ (detStep p s) ∧ (0 < dMeasure s → dMeasure (detStep p s) < dMeasure s) ∧
      (dMeasure s = 0 → detStep p s = s) := by
  obtain ⟨R, d, m, rc⟩ := s
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hp2 := (Fact.out : p.Prime).two_le
  have hp : ¬ p < 2 := by omega
  have hp0 : 0 < p := by omega
  cases R with
  | nil =>
    simp only [List.length_nil] at h1
    subst h1
    have hfix : detStep p ([], d, 0, rc) = ([], d, 0, rc) := by simp [detStep]
    rw [hfix]
    exact ⟨⟨rfl, h2, h3, h4, h5, h6, h7⟩, fun h => by simp [dMeasure] at h, fun _ => rfl⟩
  | cons r₀ rs =>
    simp only [List.length_cons] at h1
    subst h1
    have hμ : dMeasure (r₀ :: rs, d, rs.length + 1, rc) =
        (rs.length + 1) * (rs.length + 1 + 2) - rc := rfl
    have hbig : rs.length + 1 < (rs.length + 1) * (rs.length + 1 + 2) := by nlinarith
    have hne : dMeasure (r₀ :: rs, d, rs.length + 1, rc) ≠ 0 := by rw [hμ]; omega
    by_cases hmc : rs.length + 1 ≤ rc
    · -- a full round of rotations: the first column is zero
      have he : detStep p (r₀ :: rs, d, rs.length + 1, rc) = ([], 0, 0, 0) := by
        simp only [detStep, hp, hmc, if_true, if_false]
      rw [he]
      have hdet : (matOfRows p (rs.length + 1) (r₀ :: rs)).det = 0 :=
        det_matOfRows_eq_zero p rs.length _ (fun i hi => by
          rw [h6 i (by omega) hi]; simp)
      refine ⟨⟨rfl, by simp, by simp, hp0, le_rfl, fun i _ hi => absurd hi (by omega), ?_⟩,
        fun _ => by rw [hμ]; show 0 * (0 + 2) - 0 < _; omega, fun h0 => absurd h0 hne⟩
      rw [← h7, hdet]; simp
    by_cases h0 : r₀.headD 0 = 0
    · -- zero head: rotate
      have he : detStep p (r₀ :: rs, d, rs.length + 1, rc) = (rs ++ [r₀],
          if (rs.length + 1) % 2 = 0 then d * (p - 1) % p else d, rs.length + 1, rc + 1) := by
        simp only [detStep, hp, hmc, h0, if_true, if_false]
      rw [he]
      refine ⟨⟨by simp, fun r hr => h2 r (by simp at hr ⊢; tauto),
        fun r hr => h3 r (by simp at hr ⊢; tauto), ?_, by omega, ?_, ?_⟩,
        fun _ => by rw [hμ]; show _ - (rc + 1) < _; omega, fun h0' => absurd h0' hne⟩
      · split_ifs
        · exact Nat.mod_lt _ hp0
        · exact h4
      · intro i hi1 hi2
        rcases Nat.lt_or_ge i rs.length with hi | hi
        · rw [List.getD_append _ _ _ _ hi]
          simpa using h6 (i + 1) (by omega) (by omega)
        · rw [List.getD_append_right _ _ _ _ hi, show i - rs.length = 0 by omega]
          simpa using h0
      · have hpm : ((p - 1 : ℕ) : ZMod p) = -1 := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self]; simp
        rw [det_matOfRows_rotate, ← h7]
        split_ifs with hev
        · rw [Odd.neg_one_pow (Nat.odd_iff.mpr (by omega)), ZMod.natCast_mod, Nat.cast_mul, hpm]
          ring
        · rw [Even.neg_one_pow (Nat.even_iff.mpr (by omega))]
          ring
    · -- nonzero head: eliminate
      obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil (show r₀ ≠ [] by rintro rfl; simp at h0)
      have ha_lt : a < p := h3 (a :: t) (by simp) a (by simp)
      simp only [List.headD_cons] at h0 ⊢
      have ha : ((a : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; exact h0 (Nat.eq_zero_of_dvd_of_lt hd ha_lt)
      have he : detStep p ((a :: t) :: rs, d, rs.length + 1, rc) =
          (rs.map (elimRow p (a ^ (p - 2) % p) (a :: t)), d * a % p, rs.length, 0) := by
        simp only [detStep, hp, hmc, List.headD_cons, h0, if_false, Nat.add_sub_cancel]
      rw [he]
      refine ⟨⟨by simp, fun r hr => ?_, fun r hr x hx => ?_, Nat.mod_lt _ hp0, Nat.zero_le _,
        fun i _ hi => absurd hi (by omega), ?_⟩,
        fun _ => ?_, fun h0' => absurd h0' hne⟩
      · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
        rw [length_elimRow, h2 r' (by simp [hr']), h2 (a :: t) (by simp)]
        simp
      · obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr
        exact lt_of_mem_elimRow hp0 _ _ _ x hx
      · have hdet := det_matOfRows_elim (a :: t) rs (h2 (a :: t) (by simp))
          (fun r hr => h2 r (by simp [hr])) (a ^ (p - 2) % p) (by simpa using ha)
          (by simpa using natCast_pow_mod_eq_inv a ha)
        rw [← h7, hdet, ZMod.natCast_mod, Nat.cast_mul]
        simp only [List.headD_cons]
        ring
      · rw [hμ]
        show rs.length * (rs.length + 2) - 0 < _
        have : rs.length * (rs.length + 2) + (rs.length + 1) <
            (rs.length + 1) * (rs.length + 1 + 2) := by nlinarith
        omega

/-- **The determinant algorithm is polynomial-time** (infrastructure for [AB09 §7.2.4]; not
itself a result of the book).

**Proof sketch.** The initializer is two nested map loops and a count; the loop runs
`(|z| + 1)²` rounds of the polynomial-time `detWStep` (`polyTimeComputable_iterate`). States are
encodings of `(rows, d, m, rc)` satisfying `LInv`: at most `|z|` rows of at most `|z|` entries,
each below `p + 2^{|z|} + 2`, so every state has length `O(|z|³)` (`length_encState_le`). -/
theorem polyTimeComputable_detModAlg : PolyTimeComputable detModAlg := by
  have hP : PolyTimeComputable (fun z => Nat.bits (bitsVal (pairFstD z))) :=
    polyTimeComputable_normBits.comp polyTimeComputable_pairFstD
  have hentry : PolyTimeComputable entryModW :=
    polyTimeComputable_mod.comp (polyTimeComputable_pairSndD.pairEncode polyTimeComputable_pairFstD)
  have hinit : PolyTimeComputable initW :=
    hP.pairEncode (((polyTimeComputable_mapW (polyTimeComputable_mapW hentry)).comp
      (hP.pairEncode polyTimeComputable_pairSndD)).pairEncode
      ((polyTimeComputable_const [true]).pairEncode
        ((polyTimeComputable_countW.comp polyTimeComputable_pairSndD).pairEncode
          (polyTimeComputable_const []))))
  have h0 : ∀ z : List Bool,
      LInv (bitsVal (pairFstD z) + 2 ^ z.length + 2) z.length
        (initRows z, 1, (initRows z).length, 0) := by
    intro z
    have hK : (pairSndD z).length ≤ z.length := length_pairSndD_le z
    refine ⟨rfl, ?_, fun r hr => ?_, fun r hr x hx => ?_,
      by have := Nat.one_le_two_pow (n := z.length); omega, Nat.zero_le _⟩
    · simp only [initRows, List.length_map]; exact (length_decWords_le _).trans hK
    · obtain ⟨rw, hrw, rfl⟩ := List.mem_map.mp hr
      simp only [List.length_map]
      exact (length_decWords_le _).trans ((length_le_of_mem_decWords hrw).trans hK)
    · obtain ⟨rw, hrw, rfl⟩ := List.mem_map.mp hr
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have h1 := (length_le_of_mem_decWords he).trans ((length_le_of_mem_decWords hrw).trans hK)
      have h2 := (bitsVal_lt_two_pow e).trans_le (Nat.pow_le_pow_right (by norm_num) h1)
      have := Nat.mod_le (bitsVal e) (bitsVal (pairFstD z))
      omega
  have hloop := polyTimeComputable_iterate polyTimeComputable_detWStep hinit 1 2 64 3
    (fun z i _ => by
      rw [initW_eq, iterate_detWStep_encState]
      exact length_encState_le z
        (iterate_invariant (LInv _ _) (fun _ h => lInv_step _ _ _
          (by rw [Nat.add_assoc]; exact Nat.le_add_right _ _) h) i (h0 z)))
  have hsmall : PolyTimeComputable (fun z => [decide (bitsVal (pairFstD z) < 2)]) := by
    convert polyTimeComputable_lt.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_const (Nat.bits 2))) using 1
    funext z; simp [lt, bitsVal_bits]
  unfold detModAlg
  exact polyTimeComputable_ite hsmall (polyTimeComputable_const [])
    ((polyTimeComputable_pairFstD.comp polyTimeComputable_slot3).comp hloop)

/-- **The determinant algorithm is correct** (infrastructure for [AB09 §7.2.4]): for a prime
`p` and a square matrix given by its rows (every row of length `n`, the number of rows), it
outputs `Nat.bits (det M).val` for the matrix `M` over `ZMod p`.

**Proof sketch.** The rounds act on encodings as `detStep` (`iterate_detWStep_encState`). From
`(rows mod p, 1, n, 0)` the invariant `CInv` with target `det M` holds throughout, and the
potential `m(m + 2) - rc ≤ n(n + 2) < (|z| + 1)²` reaches `0`, i.e. no rows remain; then
`det [] · d = d = det M` with `d < p`, so `d = (det M).val`. -/
theorem detModAlg_pairEncode (p : ℕ) [Fact p.Prime] (rows : List (List ℕ))
    (hsq : ∀ r ∈ rows, r.length = rows.length) :
    detModAlg (pairEncode (Nat.bits p) (encMat rows)) =
      Nat.bits (matOfRows p rows.length rows).det.val := by
  have hp2 := (Fact.out : p.Prime).two_le
  set z := pairEncode (Nat.bits p) (encMat rows)
  have hfz : bitsVal (pairFstD z) = p := by simp [z, bitsVal_bits]
  have hrows : initRows z = rows.map (List.map (· % p)) := by
    simp only [initRows, z, pairSndD_pairEncode, pairFstD_pairEncode, bitsVal_bits,
      decWords_encMat, List.map_map]
    refine List.map_congr_left (fun r _ => ?_)
    simp [Function.comp_def, bitsVal_bits]
  set D₀ := (matOfRows p rows.length rows).det
  have h0 : CInv p D₀ (initRows z, 1, (initRows z).length, 0) := by
    rw [hrows]
    refine ⟨rfl, fun r hr => ?_, fun r hr x hx => ?_, by omega, Nat.zero_le _,
      fun i _ hi => absurd hi (by omega), ?_⟩
    · obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
      simp [hsq r' hr']
    · obtain ⟨r', -, rfl⟩ := List.mem_map.mp hr
      obtain ⟨x', -, rfl⟩ := List.mem_map.mp hx
      exact Nat.mod_lt _ (by omega)
    · rw [List.length_map, matOfRows_map_mod]; simp [D₀]
  have hlen : rows.length ≤ z.length := by
    have := length_decWords_le (encMat rows)
    simp only [decWords_encMat, List.length_map] at this
    simp only [z, length_pairEncode]; omega
  have hμ := iterate_measure_eq_zero (g := detStep p) (CInv p D₀) dMeasure
    (fun _ h => (cInv_step h).1) (fun _ h => (cInv_step h).2.1) (fun _ h => (cInv_step h).2.2)
    (1 * (z.length + 1) ^ 2) _ h0 (by
      show (initRows z).length * ((initRows z).length + 2) - 0 ≤ _
      rw [hrows, List.length_map]
      have := Nat.mul_le_mul hlen (Nat.add_le_add_right hlen 2)
      have h2 : z.length * (z.length + 2) + 1 = (z.length + 1) ^ 2 := by ring
      omega)
  have hI := iterate_invariant (CInv p D₀) (fun _ h => (cInv_step h).1)
    (1 * (z.length + 1) ^ 2) h0
  unfold detModAlg
  rw [hfz, if_neg (by simp; omega), initW_eq, hfz, iterate_detWStep_encState]
  generalize (detStep p)^[1 * (z.length + 1) ^ 2] (initRows z, 1, (initRows z).length, 0) = s
    at hμ hI ⊢
  obtain ⟨R, d, m, rc⟩ := s
  obtain ⟨-, -, -, h4, h5, -, h7⟩ := hI
  have hm : m = 0 := by
    simp only [dMeasure] at hμ
    by_contra hne
    have : rc < m * (m + 2) := by nlinarith [Nat.pos_of_ne_zero hne]
    omega
  subst hm
  rw [det_matOfRows_zero, one_mul] at h7
  simp only [encState, slD, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [← h7, ZMod.val_natCast_of_lt h4]

end BinArith

end Complexity
