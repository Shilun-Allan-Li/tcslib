/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.ReductionSupport
import TCSlib.Cryptography.Pseudorandom.Functions.GGM

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the GGM evaluator

The evaluator follows a path in the GGM tree on a string state containing the
current label and the remaining input. The bit-string identities connect this
implementation to the finite GGM construction.

## Main definitions

* `TCSlib.Cryptography.selHalf` selects a half of the next label.
* `TCSlib.Cryptography.ggmStep` and `TCSlib.Cryptography.ggmEval` run the tree walk.

## Main results

* `TCSlib.Cryptography.ggmEval_poly` and `TCSlib.Cryptography.ggmEval_ofFn` give
  polynomial running time and agreement with the finite evaluator.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8, Theorem 97.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, Construction 3.3.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## Bit-string identities -/

/-- Every bit of a `q·ℓ`-bit string is a bit of one of its blocks:
`w k = FunFamily.blocks q ℓ w k.divNat k.modNat` (read off `FunFamily.blocks_symm_apply`). -/
theorem eq_blocks_divNat_modNat {q ℓ : ℕ} (w : Fin (q * ℓ) → Bool) (k : Fin (q * ℓ)) :
    w k = FunFamily.blocks q ℓ w k.divNat k.modNat :=
  calc w k = (FunFamily.blocks q ℓ).symm (FunFamily.blocks q ℓ w) k := by rw [Equiv.symm_apply_apply]
    _ = FunFamily.blocks q ℓ w k.divNat k.modNat := FunFamily.blocks_symm_apply q ℓ _ k

/-- Block `k` of the encoding of a `q`-tuple of `ℓ`-bit strings (positions `ℓk, …, ℓk + ℓ − 1`)
is the encoding of the `k`-th component, read through `FunFamily.blocks` (the block window
`FunFamily.ofFn_blocks`, read backwards). -/
theorem drop_take_ofFn_blocks (q ℓ : ℕ) (w : Fin (q * ℓ) → Bool) {k : ℕ} (hk : k < q) :
    ((List.ofFn w).drop (ℓ * k)).take ℓ = List.ofFn (FunFamily.blocks q ℓ w ⟨k, hk⟩) := by
  rw [Nat.mul_comm ℓ k, FunFamily.ofFn_blocks]

/-- The encoding of the `i`-bit prefix `prefixAt x i` (`i ≤ n`) is the first `i` bits of the
encoding of `x`. -/
theorem ofFn_prefixAt {n : ℕ} (x : Fin n → Bool) {i : ℕ} (hi : i ≤ n) :
    List.ofFn (prefixAt x i) = (List.ofFn x).take i := by
  rw [take_ofFn_castLE hi]
  congr 1
  funext k
  have hk : (k : ℕ) < n := lt_of_lt_of_le k.isLt hi
  simp only [prefixAt_apply, hk, dite_true]
  rfl

/-- The first `n` bits of the encoding of a `2n`-bit string encode the first component of
`splitHalves`. -/
theorem take_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).take n = List.ofFn (splitHalves z).1 := by
  refine (take_ofFn_castLE (by omega) z).trans ?_
  exact congrArg List.ofFn (funext fun k => (splitHalves_apply_fst z k).symm)

/-- The last `n` bits of the encoding of a `2n`-bit string encode the second component of
`splitHalves`. -/
theorem drop_ofFn_splitHalves {n : ℕ} (z : Fin (2 * n) → Bool) :
    (List.ofFn z).drop n = List.ofFn (splitHalves z).2 := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_drop, List.getElem_ofFn]
  rw [splitHalves_apply_snd]

/-- **Half selection on strings:** the first (`b = false`) or the last (`b = true`) `|u|` bits
of the word `v` — `g_b(x)` of [PS10, Theorem 97.3] read off the string `g(x) = g₀(x) ‖ g₁(x)`
with the reference length `|u| = n`. -/
def selHalf (b : Bool) (u v : List Bool) : List Bool :=
  if b then (v.drop u.length).take u.length else v.take u.length

/-- Half selection on the encoding of a `2n`-bit string (reference length `n`) is the
encoding of `pairSel b (splitHalves z)`. -/
theorem selHalf_ofFn {n : ℕ} (b : Bool) {u : List Bool} (hu : u.length = n)
    (z : Fin (2 * n) → Bool) :
    selHalf b u (List.ofFn z) = List.ofFn (pairSel b (splitHalves z)) := by
  cases b
  · simp only [selHalf, pairSel_false, Bool.false_eq_true, if_false, hu, take_ofFn_splitHalves]
  · simp only [selHalf, pairSel_true, if_true, hu, drop_ofFn_splitHalves]
    exact List.take_of_length_le (le_of_eq List.length_ofFn)

/-- Half selection is at most as long as the reference word. -/
theorem length_selHalf_le (b : Bool) (u v : List Bool) : (selHalf b u v).length ≤ u.length := by
  unfold selHalf
  split_ifs <;> exact List.length_take_le _ _

/-- Half selection is polynomial-time in its three polynomial-time arguments (the typed cuts
`takeLen_poly`/`dropLen_poly` and `Complexity.polyTimeComputable_ite`). -/
theorem selHalf_poly {p : List Bool → Bool} {u v : List Bool → List Bool}
    (hp : PolyTimeComputable fun w => [p w]) (hu : PolyTimeComputable u)
    (hv : PolyTimeComputable v) : PolyTimeComputable fun w => selHalf (p w) (u w) (v w) :=
  polyTimeComputable_ite hp (takeLen_poly hu (dropLen_poly hu hv)) (takeLen_poly hu hv)

/-! ## The GGM evaluator -/

/-- **One step of the walk down the GGM tree** on the state word `⟨y, rest⟩` (current label
`y`, remaining input bits `rest`): if `rest` is empty, stay; otherwise replace `y` by the half
of `E y` selected by the head bit of `rest` (`selHalf`, reference length `|y|`) and drop that
bit. `E` is the evaluator of the length-doubling generator. -/
def ggmStep (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  if pairSndD w = [] then w
  else pairEncode (selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)))
    (pairSndD w).tail

/-- The walk down the tree from the label `y` along the bits `bs`:
`walk G' y [b₁, …, b_k] = G'_{b_k}(⋯ G'_{b₁}(y) ⋯)`. -/
def walk {S : Type} (G' : S → S × S) (y : S) (bs : List Bool) : S :=
  bs.foldl (fun y b => pairSel b (G' y)) y

/-- `ggmFrom G' x i y` is the walk from `y` along the bits of `x` from position `i` on
(strong induction on `n − i`, `ggmFrom_of_lt`, `ggmFrom_of_le`). -/
theorem ggmFrom_eq_walk {S : Type} (G' : S → S × S) {n : ℕ} (x : Fin n → Bool) :
    ∀ (i : ℕ) (y : S), ggmFrom G' x i y = walk G' y ((List.ofFn x).drop i)
  | i, y => by
    by_cases h : i < n
    · rw [ggmFrom_of_lt G' x h, ggmFrom_eq_walk G' x (i + 1)]
      have hd : (List.ofFn x).drop i = x ⟨i, h⟩ :: (List.ofFn x).drop (i + 1) := by
        rw [List.drop_eq_getElem_cons (by simpa using h), List.getElem_ofFn]
      rw [hd, walk, walk, List.foldl_cons]
    · rw [ggmFrom_of_le G' x (not_lt.1 h), List.drop_of_length_le (by simpa using not_lt.1 h)]
      rfl
termination_by i => n - i

/-- The GGM step never lengthens a word. -/
theorem length_ggmStep_le (E : List Bool → List Bool) (w : List Bool) :
    (ggmStep E w).length ≤ w.length := by
  unfold ggmStep
  split_ifs with h
  · exact le_rfl
  · obtain ⟨a, b, hw⟩ : ∃ a b, w = pairEncode a b := by
      cases hd : pairDecode w with
      | none => exact absurd (pairSndD_of_pairDecode_eq_none hd) h
      | some ab => exact ⟨ab.1, ab.2, eq_pairEncode_of_pairDecode w ab.1 ab.2 hd⟩
    subst hw
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h ⊢
    rw [length_pairEncode, length_pairEncode, List.length_tail]
    have h1 := length_selHalf_le (b.headD false) a (E a)
    have h2 : 0 < b.length := List.length_pos_of_ne_nil h
    omega

/-- The orbit of the GGM step stays within the input length. -/
theorem length_ggmStep_iterate_le (E : List Bool → List Bool) (w : List Bool) (k : ℕ) :
    ((ggmStep E)^[k] w).length ≤ w.length := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (length_ggmStep_le E _).trans ih

/-- The GGM step is polynomial-time (`Complexity.polyTimeComputable_ite` on the emptiness test
of `rest`, `selHalf_poly`, `polyTimeComputable_headD`, `Complexity.polyTimeComputable_tail`). -/
theorem ggmStep_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmStep E) := by
  have hsel : PolyTimeComputable fun w =>
      selHalf ((pairSndD w).headD false) (pairFstD w) (E (pairFstD w)) :=
    selHalf_poly (polyTimeComputable_headD.comp polyTimeComputable_pairSndD)
      polyTimeComputable_pairFstD (hE.comp polyTimeComputable_pairFstD)
  have htest : PolyTimeComputable fun w => [decide (pairSndD w = [])] :=
    polyTimeComputable_isNil.comp polyTimeComputable_pairSndD
  convert polyTimeComputable_ite htest polyTimeComputable_id
    (hsel.pairEncode
        ((polyTimeComputable_tail.congr fun _ => List.drop_one).comp
            polyTimeComputable_pairSndD)) using 1
  funext w
  simp [ggmStep]

/-- **Closed form of the GGM step's orbit on encoded data:** from `⟨s, bs⟩` with `s` an
`n`-bit label, after `k` steps the state is `⟨walk s (bs.take k), bs.drop k⟩`.

**Proof sketch.** Induction on `k`. On an empty `rest` the step is the identity and the walk
is trivial. On `b :: bs` the step replaces the label by the half of `E (ofFn s) = ofFn (G s)`
selected by `b`, which is `ofFn (pairSel b (splitHalves (G s)))` by `selHalf_ofFn`, and drops
`b`; the induction hypothesis from the new label and `bs` finishes. -/
theorem ggmStep_iterate {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s)) :
    ∀ (k : ℕ) (y : Fin n → Bool) (bs : List Bool),
      (ggmStep E)^[k] (pairEncode (List.ofFn y) bs) =
        pairEncode (List.ofFn (walk (splitHalves ∘ G) y (bs.take k))) (bs.drop k)
  | 0, y, bs => by simp [walk]
  | k + 1, y, bs => by
    rw [Function.iterate_succ_apply]
    cases bs with
    | nil =>
      have h0 : ggmStep E (pairEncode (List.ofFn y) []) = pairEncode (List.ofFn y) [] := by
        simp [ggmStep]
      rw [h0, ggmStep_iterate hG k y []]
      simp [walk]
    | cons b bs =>
      have h1 : ggmStep E (pairEncode (List.ofFn y) (b :: bs)) =
          pairEncode (List.ofFn (pairSel b (splitHalves (G y)))) bs := by
        simp only [ggmStep, pairSndD_pairEncode, pairFstD_pairEncode, List.headD_cons,
          List.tail_cons, hG]
        rw [if_neg (List.cons_ne_nil _ _), selHalf_ofFn b List.length_ofFn]
      rw [h1, ggmStep_iterate hG k]
      simp [walk, List.take_succ_cons, List.drop_succ_cons, List.foldl_cons]

/-- **The GGM evaluator** (Claim-97.c): on `⟨s, x⟩` iterate the GGM step `|⟨s, x⟩|` times
(at least `|x|`, after which the step is the identity) and read the label. -/
def ggmEval (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  pairFstD ((ggmStep E)^[w.length] w)

/-- The GGM evaluator is polynomial-time (`Complexity.polyTimeComputable_iterate` with
`R = P = var`, the orbit staying within the input length). -/
theorem ggmEval_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) :
    PolyTimeComputable (ggmEval E) := by
  have h := polyTimeComputable_iterate (ggmStep_poly hE) .var .var
    (fun x i _ => by rw [PolyExpr.eval_var]; exact length_ggmStep_iterate_le E x i)
  simp only [PolyExpr.eval_var] at h
  exact polyTimeComputable_pairFstD.comp h

/-- The GGM evaluator on `⟨s, bs⟩` with an `n`-bit label `s` and an arbitrary bit list `bs`
computes the walk from `s` along `bs` (`ggmStep_iterate`; the word is at least as long as
`bs`, so all bits are consumed). -/
theorem ggmEval_ofFn_walk {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (y : Fin n → Bool) (bs : List Bool) :
    ggmEval E (pairEncode (List.ofFn y) bs) = List.ofFn (walk (splitHalves ∘ G) y bs) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode,
    List.take_of_length_le (by rw [length_pairEncode]; omega)]

/-- **The GGM evaluator computes the GGM family:** on `⟨s, x⟩` with `s, x` `n`-bit strings it
returns the encoding of `ggmBits G s x = g_{x_n}(⋯ g_{x_1}(s) ⋯)` (`ggmStep_iterate`,
`ggmFrom_eq_walk`). -/
theorem ggmEval_ofFn {n : ℕ} {G : (Fin n → Bool) → Fin (2 * n) → Bool}
    {E : List Bool → List Bool} (hG : ∀ s : Fin n → Bool, E (List.ofFn s) = List.ofFn (G s))
    (s x : Fin n → Bool) :
    ggmEval E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (ggmBits G s x) := by
  unfold ggmEval
  rw [ggmStep_iterate hG, pairFstD_pairEncode]
  congr 1
  rw [List.take_of_length_le (by rw [length_pairEncode]; simp)]
  rw [ggmBits_def, ggm_apply, ggmFrom_eq_walk, List.drop_zero]

end TCSlib.Cryptography
