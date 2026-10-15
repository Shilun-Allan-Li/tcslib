/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.Ring
import TCSlib.Complexity.Formulas.QBF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `ψᵢ` recursion of the `TQBF` hardness proof, at the prefix level

[AB09, Theorem 4.13, the proof]: reachability within `2^i` steps is expressed by
`ψᵢ₊₁(A, B) = ∃ Z ∀ U ∀ V (((U, V) = (A, Z) ∨ (U, V) = (Z, B)) → ψᵢ(U, V))`, which keeps a
single copy of `ψᵢ`. This file proves the prenex form of that recursion correct, generically
in the one-step relation: quantifiers range over **blocks** of `w` consecutive prefix
variables, level `r` of the recursion owns three blocks `Z, U, V` (one existential block, two
universal blocks), and the matrix is the chain of selection implications closed by the
one-step relation (`levelMatrix`). The truth of the prenex formula is the midpoint recursion
`Mid` (`prefixTruth_levelMatrix`), which is a path of exactly `2^r` steps
(`mid_iff_steps`). The flat form of the matrix that a verifier checks — "some level's
selection fails, or the innermost pair is one step" — is `levelMatrix_iff_flat`.

Infrastructure for `Complexity.TQBF_PSPACEHard`; the recursion is [AB09]'s, the block
bookkeeping is not a book result.

## Main definitions

* `Complexity.TQBFHard.writeBlock`, `Complexity.TQBFHard.readBlock` — blocks of an assignment.
* `Complexity.TQBFHard.levelQuants` — the quantifier prefix of `r` levels.
* `Complexity.TQBFHard.Sel`, `Complexity.TQBFHard.levelMatrix` — the selection test and the
  prenex matrix.
* `Complexity.TQBFHard.Mid`, `Complexity.TQBFHard.Steps` — the midpoint recursion and paths
  of a given length.

## Main results

* `Complexity.TQBFHard.prefixTruth_replicate_ex`, `prefixTruth_replicate_all` — a block of
  quantifiers is a quantifier over blocks.
* `Complexity.TQBFHard.prefixTruth_levelMatrix` — the prenex `ψ_r` is the midpoint recursion.
  [AB09, Theorem 4.13, proof]
* `Complexity.TQBFHard.prefixTruth_top` — with an existential top record carrying the two
  endpoints.
* `Complexity.TQBFHard.mid_iff_steps` — the midpoint recursion is a path of `2^r` steps.
* `Complexity.TQBFHard.levelMatrix_iff_flat` — the flat form of the matrix.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13 and its proof, pp. 84-85.)
-/

namespace Complexity

namespace TQBFHard

open QBF

/-! ### Blocks of an assignment -/

/-- The assignment `σ` with the block `β` written at positions `i, …, i + |β| - 1`. -/
def writeBlock (σ : ℕ → Bool) (i : ℕ) (β : List Bool) : ℕ → Bool :=
  fun v => if i ≤ v ∧ v < i + β.length then β.getD (v - i) false else σ v

/-- The block of `w` values of `τ` at positions `i, …, i + w - 1`. -/
def readBlock (τ : ℕ → Bool) (i w : ℕ) : List Bool :=
  List.ofFn fun j : Fin w => τ (i + j)

/-- A read block has its width. -/
@[simp] theorem length_readBlock (τ : ℕ → Bool) (i w : ℕ) : (readBlock τ i w).length = w := by
  simp [readBlock]

/-- Writing a block leaves the positions below it unchanged. -/
theorem writeBlock_of_lt (σ : ℕ → Bool) (i : ℕ) (β : List Bool) {v : ℕ} (hv : v < i) :
    writeBlock σ i β v = σ v := by
  simp only [writeBlock]
  rw [if_neg (by omega)]

/-- Writing a block sets the positions inside it. -/
theorem writeBlock_of_mem (σ : ℕ → Bool) (i : ℕ) (β : List Bool) (j : ℕ) (hj : j < β.length) :
    writeBlock σ i β (i + j) = β.getD j false := by
  simp only [writeBlock]
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- Writing a one-letter-longer block is updating the first position and writing the rest
one position later. -/
theorem writeBlock_update_cons (σ : ℕ → Bool) (i : ℕ) (b : Bool) (β : List Bool) :
    writeBlock (Function.update σ i b) (i + 1) β = writeBlock σ i (b :: β) := by
  funext v
  simp only [writeBlock, List.length_cons]
  rcases lt_trichotomy v i with h | rfl | h
  · rw [if_neg (by omega), if_neg (by omega), Function.update_of_ne (by omega)]
  · rw [if_neg (by omega), if_pos (by omega), Function.update_self]
    simp
  · obtain ⟨j, rfl⟩ : ∃ j, v = i + 1 + j := ⟨v - (i + 1), by omega⟩
    by_cases hj : j < β.length
    · rw [if_pos (by omega), if_pos (by omega), show i + 1 + j - (i + 1) = j by omega,
        show i + 1 + j - i = j + 1 by omega]
      simp
    · rw [if_neg (by omega), if_neg (by omega), Function.update_of_ne (by omega)]

/-- Writing the empty block changes nothing. -/
@[simp] theorem writeBlock_nil (σ : ℕ → Bool) (i : ℕ) : writeBlock σ i [] = σ := by
  funext v
  simp only [writeBlock, List.length_nil]
  rw [if_neg (by omega)]

/-- A block is read off position by position. -/
theorem readBlock_eq {τ : ℕ → Bool} {i : ℕ} {β : List Bool}
    (h : ∀ j < β.length, τ (i + j) = β.getD j false) : readBlock τ i β.length = β := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [readBlock, List.getElem_ofFn]
  rw [h j h2]
  simp [List.getD_eq_getElem?_getD, h2]

/-- A block of a given width is read off position by position. -/
theorem readBlock_eq' {τ : ℕ → Bool} {i w : ℕ} {β : List Bool} (hw : β.length = w)
    (h : ∀ j < w, τ (i + j) = β.getD j false) : readBlock τ i w = β := by
  subst hw
  exact readBlock_eq h

/-- A block depends only on the values at its positions. -/
theorem readBlock_congr {τ τ' : ℕ → Bool} {i w : ℕ} (h : ∀ j < w, τ (i + j) = τ' (i + j)) :
    readBlock τ i w = readBlock τ' i w := by
  simp only [readBlock]
  congr 1
  funext j
  exact h j j.isLt

/-! ### Prefix truth: congruence and blocks of quantifiers -/

/-- **A block of existential quantifiers is an existential over blocks**: `w` existential
quantifiers from position `i` hold iff some block of `w` values written at `i` makes the
rest hold.

**Proof sketch.** Induction on `w`, for every assignment and start position. For `w = 0`
the only block is the empty one, and writing it changes nothing. For `w + 1`, the first
quantifier chooses a value `b` at position `i`, and the induction hypothesis, applied to the
assignment updated at `i` and the position `i + 1`, turns the remaining `w` quantifiers into
a block `β` of length `w` written from `i + 1`. Writing `β` from `i + 1` after updating
position `i` to `b` is writing the block `b :: β` from `i` (`writeBlock_update_cons`), and
`(i + 1) + w = i + (w + 1)`. Conversely, a block of length `w + 1` is `b :: β` with `β` of
length `w`, and the same two identities read backwards give the choice `b` and the
induction hypothesis's block `β`. -/
theorem prefixTruth_replicate_ex (P : (ℕ → Bool) → Prop) (w : ℕ) (rest : List Quant)
    (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth P (List.replicate w .ex ++ rest) σ i ↔
      ∃ β : List Bool, β.length = w ∧ PrefixTruth P rest (writeBlock σ i β) (i + w) := by
  induction w generalizing σ i with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero]
    constructor
    · intro h; exact ⟨[], rfl, by simpa using h⟩
    · rintro ⟨β, hβ, h⟩
      rw [List.length_eq_zero_iff] at hβ
      subst hβ
      simpa using h
  | succ w ih =>
    simp only [List.replicate_succ, List.cons_append, PrefixTruth]
    constructor
    · rintro ⟨b, hb⟩
      obtain ⟨β, hβ, h⟩ := (ih _ _).mp hb
      refine ⟨b :: β, by simp [hβ], ?_⟩
      rw [← writeBlock_update_cons, show i + (w + 1) = i + 1 + w by omega]
      exact h
    · rintro ⟨β, hβ, h⟩
      obtain ⟨b, β, rfl⟩ : ∃ b β', β = b :: β' := by
        cases β with
        | nil => simp at hβ
        | cons b β' => exact ⟨b, β', rfl⟩
      refine ⟨b, (ih _ _).mpr ⟨β, by simpa using hβ, ?_⟩⟩
      rw [writeBlock_update_cons, show i + 1 + w = i + (w + 1) by omega]
      exact h

/-- **A block of universal quantifiers is a universal over blocks**: `w` universal
quantifiers from position `i` hold iff every block of `w` values written at `i` makes the
rest hold.

**Proof sketch.** Induction on `w`, for every assignment and start position, as for
`prefixTruth_replicate_ex`. For `w = 0` the only block of length `0` is the empty one, and
writing it changes nothing. For `w + 1`, the first quantifier ranges over the value `b` at
position `i`, and the induction hypothesis, applied to the assignment updated at `i` and the
position `i + 1`, ranges over the blocks `β` of length `w` written from `i + 1`. The blocks of
length `w + 1` are exactly the `b :: β`, and writing `β` from `i + 1` after updating position
`i` to `b` is writing `b :: β` from `i` (`writeBlock_update_cons`), with
`(i + 1) + w = i + (w + 1)`; both directions are this rewriting. -/
theorem prefixTruth_replicate_all (P : (ℕ → Bool) → Prop) (w : ℕ) (rest : List Quant)
    (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth P (List.replicate w .all ++ rest) σ i ↔
      ∀ β : List Bool, β.length = w → PrefixTruth P rest (writeBlock σ i β) (i + w) := by
  induction w generalizing σ i with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.add_zero]
    constructor
    · intro h β hβ
      rw [List.length_eq_zero_iff] at hβ
      subst hβ
      simpa using h
    · intro h; simpa using h [] rfl
  | succ w ih =>
    simp only [List.replicate_succ, List.cons_append, PrefixTruth]
    constructor
    · intro h β hβ
      obtain ⟨b, β, rfl⟩ : ∃ b β', β = b :: β' := by
        cases β with
        | nil => simp at hβ
        | cons b β' => exact ⟨b, β', rfl⟩
      have := (ih _ _).mp (h b) β (by simpa using hβ)
      rwa [writeBlock_update_cons, show i + 1 + w = i + (w + 1) by omega] at this
    · intro h b
      refine (ih _ _).mpr fun β hβ => ?_
      have := h (b :: β) (by simp [hβ])
      rwa [← writeBlock_update_cons, show i + (w + 1) = i + 1 + w by omega] at this

/-- A constant hypothesis commutes with prefix truth (the quantified domain `Bool` is
nonempty). (Proved, by induction on the prefix.) -/
theorem prefixTruth_imp_const (K : Prop) (P : (ℕ → Bool) → Prop) (qs : List Quant)
    (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth (fun τ => K → P τ) qs σ i ↔ (K → PrefixTruth P qs σ i) := by
  induction qs generalizing σ i with
  | nil => exact Iff.rfl
  | cons q qs ih =>
    cases q with
    | ex =>
      simp only [PrefixTruth]
      rw [exists_congr fun b => ih _ _]
      by_cases hK : K
      · simp [hK]
      · simp [hK]
    | all =>
      simp only [PrefixTruth]
      rw [forall_congr' fun b => ih _ _]
      exact ⟨fun h hK b => h b hK, fun h b hK => h hK b⟩

/-- A constant conjunct commutes with prefix truth (the quantified domain `Bool` is
nonempty). (Proved, by induction on the prefix.) -/
theorem prefixTruth_and_const (K : Prop) (P : (ℕ → Bool) → Prop) (qs : List Quant)
    (σ : ℕ → Bool) (i : ℕ) :
    PrefixTruth (fun τ => K ∧ P τ) qs σ i ↔ (K ∧ PrefixTruth P qs σ i) := by
  induction qs generalizing σ i with
  | nil => exact Iff.rfl
  | cons q qs ih =>
    cases q with
    | ex =>
      simp only [PrefixTruth]
      rw [exists_congr fun b => ih _ _]
      exact ⟨fun ⟨b, hK, h⟩ => ⟨hK, b, h⟩, fun ⟨hK, b, h⟩ => ⟨b, hK, h⟩⟩
    | all =>
      simp only [PrefixTruth]
      rw [forall_congr' fun b => ih _ _]
      exact ⟨fun h => ⟨(h false).1, fun b => (h b).2⟩, fun h b => ⟨h.1, h.2 b⟩⟩

/-! ### The levels of the recursion -/

/-- The quantifier prefix of `r` levels of width `w`: per level, a block of `w`
existentials (the midpoint `Z`) and two blocks of `w` universals (the pair `U, V`). -/
def levelQuants (w : ℕ) : ℕ → List Quant
  | 0 => []
  | r + 1 => List.replicate w .ex ++
      (List.replicate w .all ++ (List.replicate w .all ++ levelQuants w r))

/-- The length of the prefix of `r` levels is `3wr`. -/
theorem length_levelQuants (w r : ℕ) : (levelQuants w r).length = 3 * w * r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [levelQuants, List.length_append, List.length_replicate, ih]; ring

/-- **The selection test** of [AB09]'s `∀`-folding: the pair `(U, V)` is `(A, Z)` or
`(Z, B)`. -/
def Sel (A B z u v : List Bool) : Prop := (u = A ∧ v = z) ∨ (u = z ∧ v = B)

/-- **The prenex matrix of `r` levels** of width `w` with one-step relation `E`, starting at
position `p` with the outer pair `(A, B)`: level `r + 1` reads its blocks `Z, U, V` at `p`,
`p + w`, `p + 2w`, and if `(U, V)` is selected the matrix of the remaining levels must hold
of `(U, V)` from `p + 3w`; the innermost pair must be one step. -/
def levelMatrix (w : ℕ) (E : List Bool → List Bool → Prop) :
    ℕ → ℕ → List Bool → List Bool → (ℕ → Bool) → Prop
  | 0, _, A, B, _ => E A B
  | r + 1, p, A, B, τ =>
    Sel A B (readBlock τ p w) (readBlock τ (p + w) w) (readBlock τ (p + 2 * w) w) →
      levelMatrix w E r (p + 3 * w) (readBlock τ (p + w) w) (readBlock τ (p + 2 * w) w) τ

/-- **The midpoint recursion** of [AB09, Theorem 4.13]: `Mid 0 = E`, and `Mid (r + 1) A B`
says that some block `Z` of width `w` has `Mid r A Z` and `Mid r Z B`. -/
def Mid (w : ℕ) (E : List Bool → List Bool → Prop) : ℕ → List Bool → List Bool → Prop
  | 0, A, B => E A B
  | r + 1, A, B => ∃ z : List Bool, z.length = w ∧ Mid w E r A z ∧ Mid w E r z B

/-- **The prenex `ψ_r` is the midpoint recursion** ([AB09, Theorem 4.13, the proof]): for
blocks `A, B` of width `w`, the prefix of `r` levels from position `p` holds of the level
matrix iff `Mid r A B`.

**Proof sketch.** Induction on `r`. A level is three blocks of quantifiers
(`prefixTruth_replicate_ex`, `prefixTruth_replicate_all`); once `Z, U, V` are written, the
matrix reads exactly them (`readBlock_eq`, `prefixTruth_congr_agree`), and the selection
hypothesis is a constant (`prefixTruth_imp_const`). By induction the inner prefix is
`Mid r U V`, and `∃ Z ∀ U V, Sel → Mid r U V` is `∃ Z, Mid r A Z ∧ Mid r Z B` (take
`(U, V) = (A, Z)` and `(Z, B)`). -/
theorem prefixTruth_levelMatrix (w : ℕ) (E : List Bool → List Bool → Prop) (r : ℕ) :
    ∀ (p : ℕ) (σ : ℕ → Bool) (A B : List Bool), A.length = w → B.length = w →
      (PrefixTruth (levelMatrix w E r p A B) (levelQuants w r) σ p ↔ Mid w E r A B) := by
  induction r with
  | zero => intro p σ A B _ _; exact Iff.rfl
  | succ r ih =>
    intro p σ A B hA hB
    simp only [levelQuants]
    rw [prefixTruth_replicate_ex]
    simp only [prefixTruth_replicate_all]
    -- the inner prefix, for fixed blocks
    have key : ∀ z u v : List Bool, z.length = w → u.length = w → v.length = w →
        (PrefixTruth (levelMatrix w E (r + 1) p A B) (levelQuants w r)
          (writeBlock (writeBlock (writeBlock σ p z) (p + w) u) (p + w + w) v) (p + w + w + w) ↔
          (Sel A B z u v → Mid w E r u v)) := by
      intro z u v hz hu hv
      set σ' := writeBlock (writeBlock (writeBlock σ p z) (p + w) u) (p + w + w) v
      have hread : ∀ τ : ℕ → Bool, (∀ x < p + w + w + w, τ x = σ' x) →
          readBlock τ p w = z ∧ readBlock τ (p + w) w = u ∧ readBlock τ (p + 2 * w) w = v := by
        intro τ hτ
        refine ⟨?_, ?_, ?_⟩
        · apply readBlock_eq' hz
          intro j hj
          rw [hτ _ (by omega)]
          simp only [σ']
          rw [writeBlock_of_lt _ (p + w + w) v (show p + j < p + w + w by omega),
            writeBlock_of_lt _ (p + w) u (show p + j < p + w by omega),
            writeBlock_of_mem _ p z j (by omega)]
        · apply readBlock_eq' hu
          intro j hj
          rw [hτ _ (by omega)]
          simp only [σ']
          rw [writeBlock_of_lt _ (p + w + w) v (show p + w + j < p + w + w by omega),
            writeBlock_of_mem _ (p + w) u j (by omega)]
        · apply readBlock_eq' hv
          intro j hj
          rw [hτ _ (by omega)]
          simp only [σ']
          rw [show p + 2 * w + j = p + w + w + j by omega,
            writeBlock_of_mem _ (p + w + w) v j (by omega)]
      rw [prefixTruth_congr_agree (P' := fun τ => Sel A B z u v →
          levelMatrix w E r (p + w + w + w) u v τ) _ _ _ (fun τ hτ => by
        obtain ⟨h1, h2, h3⟩ := hread τ hτ
        simp only [levelMatrix, h1, h2, h3, show p + 3 * w = p + w + w + w by omega])]
      rw [prefixTruth_imp_const, ih _ _ _ _ hu hv]
    constructor
    · rintro ⟨z, hz, h⟩
      refine ⟨z, hz, ?_, ?_⟩
      · exact ((key z A z hz hA hz).mp (h A hA z hz)) (Or.inl ⟨rfl, rfl⟩)
      · exact ((key z z B hz hz hB).mp (h z hz B hB)) (Or.inr ⟨rfl, rfl⟩)
    · rintro ⟨z, hz, h1, h2⟩
      refine ⟨z, hz, fun u hu v hv => (key z u v hz hu hv).mpr ?_⟩
      rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact h1
      · exact h2

/-- **The whole prefix**: an existential top record of three blocks (a pad `Z₀`, the source
`A` and the target `B`), followed by `R` levels. With the leaf "`I A`, `J B`, and the matrix
of the `R` levels from position `3w` on `(A, B)`", the prefix holds iff some blocks `A, B` of
width `w` have `I A`, `J B` and `Mid R A B`.

**Proof sketch.** The three existential blocks (`prefixTruth_replicate_ex`); below position
`3w` the assignment is fixed, so the leaf is `I A ∧ J B ∧ matrix` with constant conjuncts
(`prefixTruth_congr_agree`, `prefixTruth_and_const`); then `prefixTruth_levelMatrix`. -/
theorem prefixTruth_top (w : ℕ) (E : List Bool → List Bool → Prop) (I J : List Bool → Prop)
    (R : ℕ) (σ : ℕ → Bool) :
    PrefixTruth (fun τ => I (readBlock τ w w) ∧ J (readBlock τ (2 * w) w) ∧
        levelMatrix w E R (3 * w) (readBlock τ w w) (readBlock τ (2 * w) w) τ)
      (List.replicate w .ex ++ (List.replicate w .ex ++ (List.replicate w .ex ++
        levelQuants w R))) σ 0 ↔
      ∃ A B : List Bool, A.length = w ∧ B.length = w ∧ I A ∧ J B ∧ Mid w E R A B := by
  simp only [prefixTruth_replicate_ex]
  have key : ∀ z a b : List Bool, z.length = w → a.length = w → b.length = w →
      (PrefixTruth (fun τ => I (readBlock τ w w) ∧ J (readBlock τ (2 * w) w) ∧
          levelMatrix w E R (3 * w) (readBlock τ w w) (readBlock τ (2 * w) w) τ)
        (levelQuants w R)
        (writeBlock (writeBlock (writeBlock σ 0 z) (0 + w) a) (0 + w + w) b) (0 + w + w + w) ↔
        I a ∧ J b ∧ Mid w E R a b) := by
    intro z a b hz ha hb
    set σ' := writeBlock (writeBlock (writeBlock σ 0 z) (0 + w) a) (0 + w + w) b
    have hread : ∀ τ : ℕ → Bool, (∀ x < 0 + w + w + w, τ x = σ' x) →
        readBlock τ w w = a ∧ readBlock τ (2 * w) w = b := by
      intro τ hτ
      refine ⟨?_, ?_⟩
      · apply readBlock_eq' ha
        intro j hj
        rw [hτ _ (by omega)]
        simp only [σ']
        rw [writeBlock_of_lt _ (0 + w + w) b (show w + j < 0 + w + w by omega),
          show w + j = 0 + w + j by omega, writeBlock_of_mem _ (0 + w) a j (by omega)]
      · apply readBlock_eq' hb
        intro j hj
        rw [hτ _ (by omega)]
        simp only [σ']
        rw [show 2 * w + j = 0 + w + w + j by omega, writeBlock_of_mem _ (0 + w + w) b j (by omega)]
    rw [prefixTruth_congr_agree (P' := fun τ => I a ∧ J b ∧ levelMatrix w E R (0 + w + w + w) a b τ)
      _ _ _ (fun τ hτ => by
        obtain ⟨h1, h2⟩ := hread τ hτ
        rw [h1, h2, show 3 * w = 0 + w + w + w by omega])]
    rw [prefixTruth_and_const, prefixTruth_and_const, prefixTruth_levelMatrix w E R _ _ _ _ ha hb]
  constructor
  · rintro ⟨z, hz, a, ha, b, hb, h⟩
    exact ⟨a, b, ha, hb, (key z a b hz ha hb).mp h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    exact ⟨List.replicate w false, by simp, a, ha, b, hb,
      (key _ a b (by simp) ha hb).mpr h⟩

/-! ### Paths -/

/-- Paths of exactly `k` steps of `E` through blocks of width `w`. -/
def Steps (w : ℕ) (E : List Bool → List Bool → Prop) : ℕ → List Bool → List Bool → Prop
  | 0, A, B => A = B
  | k + 1, A, B => ∃ z : List Bool, z.length = w ∧ Steps w E k A z ∧ E z B

/-- **Paths compose**: between blocks of width `w`, a path of `k + m` steps is a path of `k`
steps to some block of width `w` followed by a path of `m` steps. (Proved, by induction on
`m`.) -/
theorem steps_add (w : ℕ) (E : List Bool → List Bool → Prop) (k : ℕ) :
    ∀ (m : ℕ) (A B : List Bool), A.length = w → B.length = w →
      (Steps w E (k + m) A B ↔ ∃ z : List Bool, z.length = w ∧ Steps w E k A z ∧
        Steps w E m z B) := by
  intro m
  induction m with
  | zero =>
    intro A B _ hB
    simp only [Nat.add_zero, Steps]
    exact ⟨fun h => ⟨B, hB, h, rfl⟩, fun ⟨z, _, h, hz⟩ => hz ▸ h⟩
  | succ m ih =>
    intro A B hA hB
    rw [show k + (m + 1) = (k + m) + 1 by omega]
    simp only [Steps]
    constructor
    · rintro ⟨y, hy, h1, h2⟩
      obtain ⟨z, hz, h3, h4⟩ := (ih A y hA hy).mp h1
      exact ⟨z, hz, h3, y, hy, h4, h2⟩
    · rintro ⟨z, hz, h1, y, hy, h2, h3⟩
      exact ⟨y, hy, (ih A y hA hy).mpr ⟨z, hz, h1, h2⟩, h3⟩

/-- **The midpoint recursion is a path of `2^r` steps** between blocks of width `w`.
(Proved, by induction on `r` with `steps_add`.) -/
theorem mid_iff_steps (w : ℕ) (E : List Bool → List Bool → Prop) (r : ℕ) :
    ∀ A B : List Bool, A.length = w → B.length = w →
      (Mid w E r A B ↔ Steps w E (2 ^ r) A B) := by
  induction r with
  | zero =>
    intro A B hA _
    simp only [Mid, Steps]
    exact ⟨fun h => ⟨A, hA, rfl, h⟩, fun ⟨z, _, hz, h⟩ => hz ▸ h⟩
  | succ r ih =>
    intro A B hA hB
    rw [pow_succ, Nat.mul_two, steps_add w E _ _ A B hA hB]
    simp only [Mid]
    constructor
    · rintro ⟨z, hz, h1, h2⟩
      exact ⟨z, hz, (ih A z hA hz).mp h1, (ih z B hz hB).mp h2⟩
    · rintro ⟨z, hz, h1, h2⟩
      exact ⟨z, hz, (ih A z hA hz).mpr h1, (ih z B hz hB).mpr h2⟩

/-! ### The flat matrix -/

/-- The midpoint block of record `j` (records are `3w` positions long). -/
def zRec (τ : ℕ → Bool) (w j : ℕ) : List Bool := readBlock τ (3 * w * j) w

/-- The first pair block of record `j`. -/
def uRec (τ : ℕ → Bool) (w j : ℕ) : List Bool := readBlock τ (3 * w * j + w) w

/-- The second pair block of record `j`. -/
def vRec (τ : ℕ → Bool) (w j : ℕ) : List Bool := readBlock τ (3 * w * j + 2 * w) w

/-- **The flat form of the matrix**: the matrix of `r` levels on the pair of record `j`
holds iff some level `j + i + 1` (`i < r`) is not selected by its parent `j + i`, or the
pair of record `j + r` is one step.

**Proof sketch.** Induction on `r`: an implication `S → X` is `¬S ∨ X`, and the failed
selection at the first level is the case `i = 0`. -/
theorem levelMatrix_iff_flat (w : ℕ) (E : List Bool → List Bool → Prop) (τ : ℕ → Bool)
    (r : ℕ) : ∀ j : ℕ,
      levelMatrix w E r (3 * w * (j + 1)) (uRec τ w j) (vRec τ w j) τ ↔
        (∃ i < r, ¬ Sel (uRec τ w (j + i)) (vRec τ w (j + i)) (zRec τ w (j + i + 1))
          (uRec τ w (j + i + 1)) (vRec τ w (j + i + 1))) ∨
        E (uRec τ w (j + r)) (vRec τ w (j + r)) := by
  induction r with
  | zero => intro j; simp [levelMatrix]
  | succ r ih =>
    intro j
    have hp : 3 * w * (j + 1) + 3 * w = 3 * w * (j + 1 + 1) := by ring
    simp only [levelMatrix]
    rw [hp]
    change (Sel (uRec τ w j) (vRec τ w j) (zRec τ w (j + 1)) (uRec τ w (j + 1))
        (vRec τ w (j + 1)) → levelMatrix w E r (3 * w * (j + 1 + 1)) (uRec τ w (j + 1))
          (vRec τ w (j + 1)) τ) ↔ _
    rw [ih (j + 1)]
    constructor
    · intro h
      by_cases hs : Sel (uRec τ w j) (vRec τ w j) (zRec τ w (j + 1)) (uRec τ w (j + 1))
          (vRec τ w (j + 1))
      · rcases h hs with ⟨i, hi, hn⟩ | he
        · exact Or.inl ⟨i + 1, by omega, by
            simpa only [show j + (i + 1) = j + 1 + i by omega] using hn⟩
        · exact Or.inr (by simpa only [show j + (r + 1) = j + 1 + r by omega] using he)
      · exact Or.inl ⟨0, by omega, by simpa using hs⟩
    · rintro (⟨i, hi, hn⟩ | he) hs
      · rcases i with _ | i
        · exact absurd hs (by simpa using hn)
        · exact Or.inl ⟨i, by omega, by
            simpa only [show j + (i + 1) = j + 1 + i by omega] using hn⟩
      · exact Or.inr (by simpa only [show j + (r + 1) = j + 1 + r by omega] using he)

end TQBFHard

end Complexity
