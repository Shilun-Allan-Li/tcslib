/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Logic.Relation
import TCSlib.Complexity.SpaceComplexity.Machines.VWord

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The nondeterministic walk for `PATH`: walks and the instance layout

[AB09, §4.1.2]: `PATH ∈ NL` by guessing a path vertex by vertex. This file holds the
combinatorics of the proof in `TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof`,
over the raw instance format `⟨1ⁿ, ⟨M, ⟨bits s, bits t⟩⟩⟩` (row-major adjacency word `M` of
length `n²`), so that it does not depend on `TCSlib.Complexity.SpaceComplexity.Logspace.Path`.

* **Walks.** `Complexity.WalkLe E n j c t`: `t` is reachable from `c` in at most `j` edges of
  `E` through vertices `< n`. Every reachable vertex is reachable in at most `n` edges
  (`Complexity.walkLe_short`, a pigeonhole on the sets reachable within `j` edges).
* **Layout.** `Complexity.DblAt x q u` (the input carries `dbl u ++ [0, 1]` at position `q`)
  and `Complexity.PlainAt x r u` (the input ends with `u` from position `r`), and the
  decomposition of the raw instance format into them (`Complexity.eq_pathRaw_iff`).
* **What the walk machine checks.** `Complexity.PathAcc x` — a unary prefix, a matrix field of
  `n²` aligned pairs, endpoint fields of values `s, t < n`, and a walk of at most `n` edges of
  the matrix read off the input — is membership in the raw language
  (`Complexity.pathAcc_iff`).

## Main definitions

* `Complexity.WalkLe`, `Complexity.DblAt`, `Complexity.PlainAt`.
* `Complexity.pathRaw`, `Complexity.rawEdge`, `Complexity.pathRawLang` — the raw `PATH`
  language.
* `Complexity.pathEdge`, `Complexity.UnaryRest`, `Complexity.MatRest`, `Complexity.PathAcc`.

## Main results

* `Complexity.walkLe_short`, `Complexity.reach_iff_walkLe` — path shortening.
* `Complexity.eq_pathRaw_iff` — the layout of a raw instance.
* `Complexity.pathAcc_iff` — what the machine checks is membership in `pathRawLang`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2.)
-/

namespace Complexity

open Turing

/-! ## Walks of bounded length -/

section Walks

variable (E : ℕ → ℕ → Prop) (n : ℕ)

/-- `WalkLe E n j c t`: `t` is reachable from `c` by at most `j` edges of `E`, every vertex
after `c` below `n`. -/
def WalkLe : ℕ → ℕ → ℕ → Prop
  | 0, c, t => c = t
  | j + 1, c, t => c = t ∨ ∃ v, v < n ∧ E c v ∧ WalkLe j v t

variable {E n}

/-- Every vertex reaches itself. -/
lemma walkLe_refl (j c : ℕ) : WalkLe E n j c c := by
  cases j
  · rfl
  · exact Or.inl rfl

/-- One more allowed edge. -/
lemma walkLe_succ {j c t : ℕ} (h : WalkLe E n j c t) : WalkLe E n (j + 1) c t := by
  induction j generalizing c with
  | zero => exact Or.inl h
  | succ j ih =>
    rcases h with h | ⟨v, hv, he, hw⟩
    · exact Or.inl h
    · exact Or.inr ⟨v, hv, he, ih hw⟩

/-- More allowed edges. -/
lemma walkLe_mono {j k c t : ℕ} (hjk : j ≤ k) (h : WalkLe E n j c t) : WalkLe E n k c t := by
  induction hjk with
  | refl => exact h
  | step _ ih => exact walkLe_succ ih

/-- A bounded walk from a vertex below `n` is a path of the edge relation on vertices
below `n`. -/
lemma walkLe_reach {j c t : ℕ} (hc : c < n) (h : WalkLe E n j c t) :
    Relation.ReflTransGen (fun u v => u < n ∧ v < n ∧ E u v) c t := by
  induction j generalizing c with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ j ih =>
    rcases h with rfl | ⟨v, hv, he, hw⟩
    · exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head ⟨hc, hv, he⟩ (ih hv hw)

/-- A path is a walk of some length. -/
lemma exists_walkLe {c t : ℕ}
    (h : Relation.ReflTransGen (fun u v => u < n ∧ v < n ∧ E u v) c t) :
    ∃ j, WalkLe E n j c t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨j, hj⟩ := ih
    exact ⟨j + 1, Or.inr ⟨_, hab.2.1, hab.2.2, hj⟩⟩

/-- **Path shortening**: a vertex below `n` reachable within some number of edges is
reachable within `n` edges.

**Proof sketch.** Let `S j` be the set of vertices below `n` reaching `t` within `j` edges.
The sets grow with `j`, and once `S j = S (j + 1)` they are constant from `j` on (`S (j + 2)`
is determined by `S (j + 1)` as `S (j + 1)` is by `S j`). They cannot grow strictly `n` times,
since `t ∈ S 0` and `|S j| ≤ n`; so some `j < n` has `S j = S (j + 1)`, and every `S k` is
contained in `S n`. -/
lemma walkLe_short {j c t : ℕ} (ht : t < n) (hc : c < n) (h : WalkLe E n j c t) :
    WalkLe E n n c t := by
  classical
  let S : ℕ → Finset ℕ := fun j => (Finset.range n).filter fun c => WalkLe E n j c t
  have memS : ∀ j c, c ∈ S j ↔ c < n ∧ WalkLe E n j c t := by
    intro j c; simp [S]
  have hmono : ∀ j k, j ≤ k → S j ⊆ S k := by
    intro j k hjk c hcj
    rw [memS] at hcj ⊢
    exact ⟨hcj.1, walkLe_mono hjk hcj.2⟩
  have hstab : ∀ j, S j = S (j + 1) → S (j + 1) = S (j + 2) := by
    intro j he
    ext c
    rw [memS, memS]
    have key : ∀ v, v < n → (WalkLe E n (j + 1) v t ↔ WalkLe E n j v t) := by
      intro v hv
      have := congrArg (fun S : Finset ℕ => v ∈ S) he
      simp only [memS, eq_iff_iff] at this
      exact ⟨fun h => (this.mpr ⟨hv, h⟩).2, fun h => (this.mp ⟨hv, h⟩).2⟩
    constructor
    · rintro ⟨hc, h | ⟨v, hv, he, hw⟩⟩
      · exact ⟨hc, Or.inl h⟩
      · exact ⟨hc, Or.inr ⟨v, hv, he, (key v hv).mpr hw⟩⟩
    · rintro ⟨hc, h | ⟨v, hv, he, hw⟩⟩
      · exact ⟨hc, Or.inl h⟩
      · exact ⟨hc, Or.inr ⟨v, hv, he, (key v hv).mp hw⟩⟩
  have hex : ∃ j₀, j₀ ≤ n ∧ S j₀ = S (j₀ + 1) := by
    by_contra hne
    push_neg at hne
    have hcard : ∀ j, j ≤ n → j + 1 ≤ (S j).card := by
      intro j hj
      induction j with
      | zero =>
        exact Finset.card_pos.mpr ⟨t, (memS 0 t).mpr ⟨ht, rfl⟩⟩
      | succ j ih =>
        have hlt : (S j).card < (S (j + 1)).card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
            ⟨hmono j (j + 1) (by omega), hne j (by omega)⟩)
        have := ih (by omega)
        omega
    have h1 := hcard n le_rfl
    have h2 : (S n).card ≤ n := by
      calc (S n).card ≤ (Finset.range n).card := Finset.card_filter_le _ _
        _ = n := Finset.card_range n
    omega
  obtain ⟨j₀, hj₀, he⟩ := hex
  have hconst : ∀ i, S (j₀ + i) = S (j₀ + i + 1) := by
    intro i
    induction i with
    | zero => exact he
    | succ i ih => exact hstab (j₀ + i) ih
  have hfix : ∀ i, S (j₀ + i) = S j₀ := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [← Nat.add_assoc, ← hconst i, ih]
  have hsub : S j ⊆ S n := by
    rcases Nat.le_total j n with hjn | hnj
    · exact hmono j n hjn
    · obtain ⟨i, rfl⟩ : ∃ i, j = j₀ + i := ⟨j - j₀, by omega⟩
      rw [hfix i]
      exact hmono j₀ n hj₀
  exact ((memS n c).mp (hsub ((memS j c).mpr ⟨hc, h⟩))).2

/-- **Reachability is walking within `n` edges** (for endpoints below `n`). -/
lemma reach_iff_walkLe {c t : ℕ} (hc : c < n) (ht : t < n) :
    Relation.ReflTransGen (fun u v => u < n ∧ v < n ∧ E u v) c t ↔ WalkLe E n n c t := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := exists_walkLe h
    exact walkLe_short ht hc hj
  · exact walkLe_reach hc

end Walks

/-! ## The layout of an instance -/

section Layout

/-- A `true` bit read with default `false` is inside the word. -/
lemma lt_of_getD_true {l : List Bool} {i : ℕ} (h : l.getD i false = true) : i < l.length := by
  by_contra hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
  simp at h

/-- Two words agreeing in length and at every position are equal. -/
lemma ext_getD' {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length)
    (h : ∀ i < l₁.length, l₁.getD i false = l₂.getD i false) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro i h1 h2
  have := h i h1
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this

/-- `DblAt x q u`: the input `x` carries `dbl u` followed by the separator `[0, 1]` at
position `q`. -/
def DblAt (x : List Bool) (q : ℕ) (u : List Bool) : Prop :=
  (∀ i < u.length, x.getD (q + 2 * i) false = u.getD i false ∧
    x.getD (q + 2 * i + 1) false = u.getD i false) ∧
  x.getD (q + 2 * u.length) false = false ∧ x.getD (q + 2 * u.length + 1) false = true

/-- `PlainAt x r u`: the input `x` ends with `u`, from position `r`. -/
def PlainAt (x : List Bool) (r : ℕ) (u : List Bool) : Prop :=
  (∀ i < u.length, x.getD (r + i) false = u.getD i false) ∧ x.length = r + u.length

/-- Dropping the first component of a pair. -/
private lemma drop_pairEncode (u w : List Bool) : (pairEncode u w).drop (2 * u.length + 2) = w := by
  rw [pairEncode_eq_dbl, List.drop_left']
  simp

/-- **The layout at a position**: `x` carries `dbl u ++ [0, 1]` at `q` iff the suffix from
`q` is a pair with first component `u`.

**Proof sketch.** Read positions of the suffix with `pairEncode_getD`; conversely the
separator bit `1` places `q + 2|u| + 1` inside `x`, the lengths agree, and every position
of the suffix is a doubled bit, a separator bit, or a bit of the rest. -/
lemma dblAt_iff (x : List Bool) (q : ℕ) (u : List Bool) :
    DblAt x q u ↔ x.drop q = pairEncode u (x.drop (q + 2 * u.length + 2)) := by
  constructor
  · rintro ⟨hb, h0, h1⟩
    have hlen := lt_of_getD_true h1
    refine ext_getD' (by simp only [List.length_drop, length_pairEncode]; omega) fun i _ => ?_
    rw [getD_drop, pairEncode_getD]
    split_ifs with c1 c2 c3
    · have := hb (i / 2) (by omega)
      rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [show q + i = q + 2 * (i / 2) by omega]; exact this.1
      · rw [show q + i = q + 2 * (i / 2) + 1 by omega]; exact this.2
    · subst c2; exact h0
    · subst c3; rw [← Nat.add_assoc]; exact h1
    · rw [getD_drop]; congr 1; omega
  · intro h
    have key : ∀ j, x.getD (q + j) false = (pairEncode u (x.drop (q + 2 * u.length + 2))).getD j
        false := by intro j; rw [← h, getD_drop]
    refine ⟨fun i hi => ⟨?_, ?_⟩, ?_, ?_⟩
    · rw [key, pairEncode_getD, if_pos (by omega)]; congr 1; omega
    · rw [Nat.add_assoc, key, pairEncode_getD, if_pos (by omega)]; congr 1; omega
    · rw [key, pairEncode_getD, if_neg (by omega), if_pos rfl]
    · rw [Nat.add_assoc, key, pairEncode_getD, if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- The input ends with `u` from position `r` iff `r` is inside and the suffix is `u`. -/
lemma plainAt_iff (x : List Bool) (r : ℕ) (u : List Bool) :
    PlainAt x r u ↔ r ≤ x.length ∧ x.drop r = u := by
  constructor
  · rintro ⟨hb, hl⟩
    refine ⟨by omega, ext_getD' (by simp; omega) fun i hi => ?_⟩
    rw [getD_drop]
    exact hb i (by simp at hi; omega)
  · rintro ⟨hr, rfl⟩
    refine ⟨fun i hi => by rw [getD_drop], by simp; omega⟩

/-- **The raw `PATH` instance** `⟨1ⁿ, ⟨M, ⟨bits s, bits t⟩⟩⟩`. -/
def pathRaw (n : ℕ) (M : List Bool) (s t : ℕ) : List Bool :=
  pairEncode (List.replicate n true) (pairEncode M (pairEncode (Nat.bits s) (Nat.bits t)))

/-- The edge relation of the row-major adjacency word `M` on vertices below `n`. -/
def rawEdge (n : ℕ) (M : List Bool) (u v : ℕ) : Prop :=
  u < n ∧ v < n ∧ M.getD (u * n + v) false = true

/-- **The raw `PATH` language**: raw instances (matrix word of length `n²`, endpoints
below `n`) whose target is reachable from their source. -/
def pathRawLang : Language Bool :=
  {x | ∃ (n : ℕ) (M : List Bool) (s t : ℕ), M.length = n * n ∧ s < n ∧ t < n ∧
    x = pathRaw n M s t ∧ Relation.ReflTransGen (rawEdge n M) s t}

/-- **The layout of a raw instance**: `x = ⟨1ⁿ, ⟨M, ⟨bits s, bits t⟩⟩⟩` iff `x` carries the
four fields at the positions `0`, `2n + 2`, `2n + 2 + 2|M| + 2` and
`2n + 2 + 2|M| + 2 + 2|bits s| + 2`.

**Proof sketch.** `dblAt_iff` three times and `plainAt_iff` once, peeling one pair at a
time (`drop_pairEncode`, `List.drop_drop`). -/
lemma eq_pathRaw_iff (x : List Bool) (n : ℕ) (M : List Bool) (s t : ℕ) :
    x = pathRaw n M s t ↔
      DblAt x 0 (List.replicate n true) ∧ DblAt x (2 * n + 2) M ∧
      DblAt x (2 * n + 2 + 2 * M.length + 2) (Nat.bits s) ∧
      PlainAt x (2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2) (Nat.bits t) := by
  constructor
  · rintro rfl
    have d1 : (pathRaw n M s t).drop (2 * n + 2) =
        pairEncode M (pairEncode (Nat.bits s) (Nat.bits t)) := by
      have := drop_pairEncode (List.replicate n true)
        (pairEncode M (pairEncode (Nat.bits s) (Nat.bits t)))
      simpa using this
    have d2 : (pathRaw n M s t).drop (2 * n + 2 + 2 * M.length + 2) =
        pairEncode (Nat.bits s) (Nat.bits t) := by
      rw [show 2 * n + 2 + 2 * M.length + 2 = (2 * n + 2) + (2 * M.length + 2) by omega,
        ← List.drop_drop, d1, drop_pairEncode]
    have d3 : (pathRaw n M s t).drop
        (2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2) = Nat.bits t := by
      rw [show 2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2 =
        (2 * n + 2 + 2 * M.length + 2) + (2 * (Nat.bits s).length + 2) by omega,
        ← List.drop_drop, d2, drop_pairEncode]
    refine ⟨(dblAt_iff _ _ _).mpr ?_, (dblAt_iff _ _ _).mpr ?_, (dblAt_iff _ _ _).mpr ?_,
      (plainAt_iff _ _ _).mpr ⟨?_, d3⟩⟩
    · simp only [List.drop_zero, Nat.zero_add, List.length_replicate]
      rw [show (pathRaw n M s t).drop (2 * n + 2) = _ from d1]; rfl
    · rw [d1, show 2 * n + 2 + 2 * M.length + 2 = (2 * n + 2) + (2 * M.length + 2) by omega,
        ← List.drop_drop, d1, drop_pairEncode]
    · rw [d2, show 2 * n + 2 + 2 * M.length + 2 + 2 * (Nat.bits s).length + 2 =
        (2 * n + 2 + 2 * M.length + 2) + (2 * (Nat.bits s).length + 2) by omega,
        ← List.drop_drop, d2, drop_pairEncode]
    · simp [pathRaw, length_pairEncode]; omega
  · rintro ⟨h1, h2, h3, h4⟩
    rw [dblAt_iff] at h1 h2 h3
    rw [plainAt_iff] at h4
    simp only [List.drop_zero, Nat.zero_add, List.length_replicate] at h1
    rw [h1, h2, h3, h4.2]
    rfl

/-- A row-major index is below `n²`. -/
lemma rowMajor_lt {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n := by
  have : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n hu
  rw [Nat.succ_mul] at this
  omega

end Layout

/-! ## What the machine checks -/

/-- The matrix bit of the edge `u → v`, read off the input at its row-major position. -/
def pathEdge (x : List Bool) (n u v : ℕ) : Prop :=
  x.getD (2 * n + 2 + 2 * (u * n + v)) false = true

/-- The unary prefix from pair `k` on: aligned `11` pairs up to pair `n`, then `01`. -/
def UnaryRest (x : List Bool) (k n : ℕ) : Prop :=
  (∀ i, k ≤ i → i < n → x.getD (2 * i) false = true ∧ x.getD (2 * i + 1) false = true) ∧
  x.getD (2 * n) false = false ∧ x.getD (2 * n + 1) false = true

/-- The matrix field from pair `i` on: aligned data pairs up to pair `n²`, then `01`. -/
def MatRest (x : List Bool) (n i : ℕ) : Prop :=
  (∀ j, i ≤ j → j < n * n →
    x.getD (2 * n + 2 + 2 * j) false = x.getD (2 * n + 2 + 2 * j + 1) false) ∧
  x.getD (2 * n + 2 + 2 * (n * n)) false = false ∧
  x.getD (2 * n + 2 + 2 * (n * n) + 1) false = true

/-- **What the walk machine accepts**: a unary prefix `1ⁿ`, a matrix field of `n²` aligned
pairs, a doubled source field `bits s` and a plain target field `bits t` ending the input,
with `s, t < n` and `t` reachable from `s` within `n` edges of `pathEdge`. -/
def PathAcc (x : List Bool) : Prop :=
  ∃ n, UnaryRest x 0 n ∧ MatRest x n 0 ∧
    ∃ s, s < n ∧ DblAt x (2 * n + 2 + 2 * (n * n) + 2) (Nat.bits s) ∧
      ∃ t, t < n ∧
        PlainAt x (2 * n + 2 + 2 * (n * n) + 2 + 2 * (Nat.bits s).length + 2) (Nat.bits t) ∧
        WalkLe (pathEdge x n) n n s t

/-- The unary prefix is the doubled word `1ⁿ` followed by the separator. -/
lemma unaryRest_iff (x : List Bool) (n : ℕ) :
    UnaryRest x 0 n ↔ DblAt x 0 (List.replicate n true) := by
  have hr : ∀ i < n, (List.replicate n true).getD i false = true := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl
  simp only [UnaryRest, DblAt, List.length_replicate, Nat.zero_add, Nat.zero_le, true_imp_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i hi => by rw [hr i hi]; exact h1 i hi, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun i hi => by rw [← hr i hi]; exact h1 i hi, h2, h3⟩

/-- The matrix field is a doubled word of length `n²` followed by the separator. -/
lemma matRest_iff (x : List Bool) (n : ℕ) :
    MatRest x n 0 ↔ ∃ M : List Bool, M.length = n * n ∧ DblAt x (2 * n + 2) M := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    let M := (List.range (n * n)).map fun j => x.getD (2 * n + 2 + 2 * j) false
    have hM : M.length = n * n := by simp [M]
    have hg : ∀ j < n * n, M.getD j false = x.getD (2 * n + 2 + 2 * j) false := by
      intro j hj
      simp [M, List.getD_eq_getElem?_getD, List.getElem?_range hj]
    refine ⟨M, hM, fun i hi => ?_, by rw [hM]; exact h2, by rw [hM]; exact h3⟩
    rw [hM] at hi
    rw [hg i hi]
    exact ⟨rfl, (h1 i (Nat.zero_le _) hi).symm⟩
  · rintro ⟨M, hM, h1, h2, h3⟩
    rw [hM] at h1 h2 h3
    refine ⟨fun j _ hj => ?_, h2, h3⟩
    have := h1 j hj
    rw [this.1, this.2]

/-- **`PathAcc` is membership in the raw `PATH` language.**

**Proof sketch.** `eq_pathRaw_iff` matches the four fields; the matrix word is read off the
input (`matRest_iff`), so `pathEdge` is its edge relation below `n`; reachability is walking
within `n` edges (`reach_iff_walkLe`). -/
theorem pathAcc_iff (x : List Bool) : PathAcc x ↔ x ∈ pathRawLang := by
  have hedge : ∀ n (M : List Bool), M.length = n * n → DblAt x (2 * n + 2) M →
      ∀ u v, u < n → v < n → (pathEdge x n u v ↔ M.getD (u * n + v) false = true) := by
    intro n M hM hD u v hu hv
    have := (hD.1 (u * n + v) (by rw [hM]; exact rowMajor_lt hu hv)).1
    simp only [pathEdge, this]
  constructor
  · rintro ⟨n, hU, hMat, s, hs, hD, t, ht, hP, hW⟩
    obtain ⟨M, hM, hDM⟩ := (matRest_iff x n).mp hMat
    refine ⟨n, M, s, t, hM, hs, ht, (eq_pathRaw_iff x n M s t).mpr
      ⟨(unaryRest_iff x n).mp hU, hDM, by rwa [hM], by rwa [hM]⟩, ?_⟩
    refine ((reach_iff_walkLe hs ht).mpr hW).mono fun u v ⟨hu, hv, he⟩ => ?_
    exact ⟨hu, hv, (hedge n M hM hDM u v hu hv).mp he⟩
  · rintro ⟨n, M, s, t, hM, hs, ht, hx, hr⟩
    obtain ⟨h1, h2, h3, h4⟩ := (eq_pathRaw_iff x n M s t).mp hx
    rw [hM] at h3 h4
    refine ⟨n, (unaryRest_iff x n).mpr h1, (matRest_iff x n).mpr ⟨M, hM, h2⟩, s, hs, h3, t, ht,
      h4, (reach_iff_walkLe hs ht).mp (hr.mono fun u v ⟨hu, hv, he⟩ => ?_)⟩
    exact ⟨hu, hv, (hedge n M hM h2 u v hu hv).mpr he⟩

/-! ## Fields and counters -/

/-- The binary digits of a positive number: its parity, then the digits of its half. -/
lemma bits_eq_cons {w : ℕ} (hw : w ≠ 0) :
    Nat.bits w = decide (w % 2 = 1) :: Nat.bits (w / 2) := by
  have h1 := LogProg.bits_head_odd w
  rw [if_neg hw] at h1
  have h2 := LogProg.bits_half w
  cases hl : Nat.bits w with
  | nil => rw [hl] at h1; simp at h1
  | cons b t =>
    rw [hl] at h1 h2
    simp only [List.head?_cons, Option.some.injEq, List.tail_cons] at h1 h2
    rw [h1, h2]

/-- A doubled field with a first bit. -/
lemma dblAt_cons (x : List Bool) (q : ℕ) (b : Bool) (u : List Bool) :
    DblAt x q (b :: u) ↔
      (x.getD q false = b ∧ x.getD (q + 1) false = b) ∧ DblAt x (q + 2) u := by
  simp only [DblAt, List.length_cons]
  have e1 : ∀ i, q + 2 * (i + 1) = q + 2 + 2 * i := fun i => by ring
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, ?_, ?_⟩
    · have := h1 (i + 1) (by omega)
      rw [e1, List.getD_cons_succ] at this
      exact this
    · rw [← e1]; exact h2
    · rw [← e1]; exact h3
  · rintro ⟨⟨h0, h0'⟩, h1, h2, h3⟩
    refine ⟨fun i hi => ?_, by rw [e1]; exact h2, by rw [e1]; exact h3⟩
    cases i with
    | zero => simpa using ⟨h0, h0'⟩
    | succ i => rw [e1, List.getD_cons_succ]; exact h1 i (by omega)

/-- A plain suffix with a first bit. -/
lemma plainAt_cons (x : List Bool) (r : ℕ) (b : Bool) (u : List Bool) :
    PlainAt x r (b :: u) ↔ x.getD r false = b ∧ PlainAt x (r + 1) u := by
  simp only [PlainAt, List.length_cons]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by simpa using h1 0 (by omega), fun i hi => ?_, by omega⟩
    have := h1 (i + 1) (by omega)
    rw [← Nat.add_assoc, List.getD_cons_succ] at this
    rw [Nat.add_assoc, Nat.add_comm 1 i, ← Nat.add_assoc]; exact this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun i hi => ?_, by omega⟩
    cases i with
    | zero => simpa using h0
    | succ i => rw [show r + (i + 1) = r + 1 + i by omega, List.getD_cons_succ]; exact h1 i (by omega)

/-- Advancing a row-major counter: the column wraps at `n` into the next row. -/
lemma divmod_succ {n i : ℕ} (hn : 0 < n) :
    (i % n + 1 = n → (i + 1) / n = i / n + 1 ∧ (i + 1) % n = 0) ∧
    (i % n + 1 ≠ n → (i + 1) / n = i / n ∧ (i + 1) % n = i % n + 1) := by
  have h1 := Nat.div_add_mod i n
  have h2 := Nat.mod_lt i hn
  refine ⟨fun h => (Nat.div_mod_unique hn).mpr ⟨?_, hn⟩, fun h => (Nat.div_mod_unique hn).mpr
    ⟨by omega, by omega⟩⟩
  rw [Nat.mul_succ]; omega

/-- The row counter reaches `n` exactly at pair `n²`. -/
lemma div_eq_self_iff {n i : ℕ} (hi : i ≤ n * n) : i / n = n ↔ i = n * n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at hi ⊢; omega
  · constructor
    · intro h
      have := Nat.div_mul_le_self i n
      rw [h] at this; omega
    · rintro rfl; exact Nat.mul_div_cancel n hn

end Complexity
