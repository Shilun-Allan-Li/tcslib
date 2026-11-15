/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.SpaceComplexity.Logspace.Path

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The language `UPATH`

[AB09, §7.7, p.139]: `UPATH` is "the restriction of the NL-complete PATH problem to undirected
graphs": given an `n`-vertex undirected graph `G` and vertices `s`, `t`, is `s` connected to
`t`? Instances use the encoding `Complexity.encodePATH` of `Complexity.PATH` (unary vertex
count, row-major adjacency matrix, endpoints in binary); an undirected graph is a symmetric
adjacency matrix. This file defines the language and reads an instance off the input the way
the random-walk machine of `TCSlib.Complexity.Randomized.UPathRL` checks it.

## Main definitions

* `Complexity.UPATH` — the language. [AB09, §7.7]
* `Complexity.inEdge`, `Complexity.SymRest`, `Complexity.UShape` — the edge relation, its
  symmetry, and the field layout, read off the input.

## Main results

* `Complexity.UPATH_subset_PATH` — `UPATH` is a restriction of `PATH`.
* `Complexity.ushape_unique` — the layout determines `n`, `s`, `t`.
* `Complexity.mem_UPATH_iff` — membership is a symmetric layout with `t` reachable from `s`.

## Divergences

* [AB09] does not fix an encoding. A matrix that is not symmetric encodes no undirected graph,
  so such strings are not in `UPATH` (as strings encoding no instance at all are not); `UPATH`
  is thus `PATH` intersected with the symmetric encodings. Loops (`A u u = 1`) are allowed and
  harmless.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.7, Theorem 7.19.)
-/

namespace Complexity

/-- **The language `UPATH`** [AB09, §7.7, p.139]: encodings `⟨G, s, t⟩` of undirected graphs
(symmetric adjacency matrices) in which `t` is reachable from `s`. -/
def UPATH : Language Bool :=
  {x | ∃ (n : ℕ) (A : Fin n → Fin n → Bool) (s t : Fin n),
    x = encodePATH n A s t ∧ (∀ u v, A u v = A v u) ∧ GraphReach A s t}

/-- `UPATH` is the restriction of `PATH` to undirected graphs. [AB09, §7.7] -/
theorem UPATH_subset_PATH {x : List Bool} (h : x ∈ UPATH) : x ∈ PATH := by
  obtain ⟨n, A, s, t, hx, -, hr⟩ := h
  exact ⟨n, A, s, t, hx, hr⟩

/-- The edge relation of the matrix field of the input, on `Fin n`. -/
def inEdge (x : List Bool) (n : ℕ) (u v : Fin n) : Prop := pathEdge x n u v

/-- The input's edge relation is decidable (it reads one input bit). -/
instance (x : List Bool) (n : ℕ) : DecidableRel (inEdge x n) := fun u v => by
  unfold inEdge pathEdge; infer_instance

/-- The matrix field of the input is symmetric on vertices below `n`. -/
def SymRest (x : List Bool) (n : ℕ) : Prop :=
  ∀ u v, u < n → v < n → (pathEdge x n u v ↔ pathEdge x n v u)

/-- Symmetry of the matrix field makes the edge relation symmetric. -/
lemma symmetric_inEdge {x : List Bool} {n : ℕ} (h : SymRest x n) : Symmetric (inEdge x n) :=
  fun u v huv => (h u v u.isLt v.isLt).mp huv

/-- **The layout of an instance**, as the machine checks it: a unary prefix `1ⁿ`, a matrix
field of `n²` aligned pairs, a doubled source field `bits s` and a plain target field
`bits t` ending the input, with `s, t < n`. -/
def UShape (x : List Bool) (n s t : ℕ) : Prop :=
  UnaryRest x 0 n ∧ MatRest x n 0 ∧ s < n ∧
    DblAt x (2 * n + 2 + 2 * (n * n) + 2) (Nat.bits s) ∧ t < n ∧
    PlainAt x (2 * n + 2 + 2 * (n * n) + 2 + 2 * (Nat.bits s).length + 2) (Nat.bits t)

/-- The unary prefix determines `n`. -/
lemma unaryRest_unique {x : List Bool} {n n' : ℕ} (h : UnaryRest x 0 n)
    (h' : UnaryRest x 0 n') : n = n' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have := (h'.1 n (Nat.zero_le _) hlt).1; rw [h.2.1] at this; simp at this
  · have := (h.1 n' (Nat.zero_le _) hlt).1; rw [h'.2.1] at this; simp at this

/-- A doubled field followed by the separator determines its word. -/
lemma dblAt_unique {x : List Bool} : ∀ {q : ℕ} {u u' : List Bool}, DblAt x q u →
    DblAt x q u' → u = u'
  | q, [], [], _, _ => rfl
  | q, [], b :: u', h, h' => by
    rw [dblAt_cons] at h'
    have h0 := h.2.1; have h1 := h.2.2
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at h0 h1
    rw [h'.1.1] at h0; rw [h'.1.2] at h1; subst h0; simp at h1
  | q, b :: u, [], h, h' => by
    rw [dblAt_cons] at h
    have h0 := h'.2.1; have h1 := h'.2.2
    simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at h0 h1
    rw [h.1.1] at h0; rw [h.1.2] at h1; subst h0; simp at h1
  | q, b :: u, b' :: u', h, h' => by
    rw [dblAt_cons] at h h'
    rw [← h.1.1, h'.1.1, dblAt_unique h.2 h'.2]

/-- A plain suffix determines its word. -/
lemma plainAt_unique {x : List Bool} {r : ℕ} {u u' : List Bool} (h : PlainAt x r u)
    (h' : PlainAt x r u') : u = u' :=
  ((plainAt_iff x r u).mp h).2.symm.trans ((plainAt_iff x r u').mp h').2

/-- **The layout determines the instance**: `n`, `s` and `t` are unique. -/
theorem ushape_unique {x : List Bool} {n s t n' s' t' : ℕ} (h : UShape x n s t)
    (h' : UShape x n' s' t') : n = n' ∧ s = s' ∧ t = t' := by
  obtain rfl := unaryRest_unique h.1 h'.1
  obtain rfl := LogProg.bits_injective (dblAt_unique h.2.2.2.1 h'.2.2.2.1)
  exact ⟨rfl, rfl, LogProg.bits_injective (plainAt_unique h.2.2.2.2.2 h'.2.2.2.2.2)⟩

/-- **An encoding has its layout**, and its edges are those of its matrix.

**Proof sketch.** `encodePATH` is the raw instance `pathRaw` of the adjacency word, whose
fields `eq_pathRaw_iff` places; the matrix field is read by `matRest_iff` and its bits by
`adjWord_getD`. -/
lemma ushape_of_eq {x : List Bool} {n : ℕ} {A : Fin n → Fin n → Bool} {s t : Fin n}
    (hx : x = encodePATH n A s t) :
    UShape x n s t ∧ ∀ u v : Fin n, inEdge x n u v ↔ A u v = true := by
  have hM := length_adjWord n A
  obtain ⟨h1, h2, h3, h4⟩ := (eq_pathRaw_iff x n _ s t).mp hx
  rw [hM] at h3 h4
  refine ⟨⟨(unaryRest_iff x n).mpr h1, (matRest_iff x n).mpr ⟨_, hM, h2⟩, s.isLt, h3, t.isLt,
    h4⟩, fun u v => ?_⟩
  have := (h2.1 (u * n + v) (by rw [hM]; exact rowMajor_lt u.isLt v.isLt)).1
  simp only [inEdge, pathEdge, this, adjWord_getD]

/-- **The layout gives an encoding**: a string with the layout of `n`, `s`, `t` encodes the
matrix of its matrix field.

**Proof sketch.** Read the matrix word `M` off the field (`matRest_iff`) and set
`A u v = M[u · n + v]`; every index below `n²` is `(i / n) · n + i % n`, so `M` is the
adjacency word of `A`, and `eq_pathRaw_iff` reassembles the instance. -/
lemma exists_eq_of_ushape {x : List Bool} {n s t : ℕ} (h : UShape x n s t) :
    ∃ A : Fin n → Fin n → Bool, x = encodePATH n A ⟨s, h.2.2.1⟩ ⟨t, h.2.2.2.2.1⟩ ∧
      ∀ u v : Fin n, inEdge x n u v ↔ A u v = true := by
  obtain ⟨hU, hMat, hs, hD, ht, hP⟩ := h
  obtain ⟨M, hM, hDM⟩ := (matRest_iff x n).mp hMat
  let A : Fin n → Fin n → Bool := fun u v => M.getD (u * n + v) false
  have hAM : ((List.finRange n).flatMap fun u => (List.finRange n).map (A u)) = M := by
    refine ext_getD' (by rw [length_adjWord, hM]) fun i hi => ?_
    rw [length_adjWord] at hi
    have hn : 0 < n := Nat.pos_of_ne_zero fun h0 => by subst h0; simp at hi
    have he : i = (i / n) * n + i % n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod i n).symm
    have := adjWord_getD A ⟨i / n, Nat.div_lt_of_lt_mul hi⟩ ⟨i % n, Nat.mod_lt i hn⟩
    simp only at this
    rw [← he] at this
    rw [this]
    simp only [A]
    rw [← he]
  refine ⟨A, ?_, fun u v => ?_⟩
  · have hx : x = pathRaw n M s t := (eq_pathRaw_iff x n M s t).mpr
      ⟨(unaryRest_iff x n).mp hU, hDM, by rw [hM]; exact hD, by rw [hM]; exact hP⟩
    exact hx.trans (by rw [← hAM]; rfl)
  · have := (hDM.1 (u * n + v) (by rw [hM]; exact rowMajor_lt u.isLt v.isLt)).1
    simp only [inEdge, pathEdge, this, A]

/-- **Membership in `UPATH`**: `x` has the layout of some `n`, `s`, `t`, its matrix field is
symmetric, and `t` is reachable from `s` along its edges.

**Proof sketch.** For an encoded instance, `ushape_of_eq` gives the layout and identifies the
edges `inEdge` with the matrix entries, so symmetry of the matrix is `SymRest` and
reachability transfers; conversely `exists_eq_of_ushape` rebuilds the matrix from the
layout. -/
theorem mem_UPATH_iff (x : List Bool) :
    x ∈ UPATH ↔ ∃ (n s t : ℕ) (h : UShape x n s t), SymRest x n ∧
      Relation.ReflTransGen (inEdge x n) ⟨s, h.2.2.1⟩ ⟨t, h.2.2.2.2.1⟩ := by
  constructor
  · rintro ⟨n, A, s, t, hx, hA, hr⟩
    obtain ⟨hS, hE⟩ := ushape_of_eq hx
    refine ⟨n, s, t, hS, fun u v hu hv => ?_, ?_⟩
    · have e1 := hE ⟨u, hu⟩ ⟨v, hv⟩
      have e2 := hE ⟨v, hv⟩ ⟨u, hu⟩
      simp only [inEdge] at e1 e2
      rw [e1, e2, hA]
    · exact hr.mono fun u v h => (hE u v).mpr h
  · rintro ⟨n, s, t, hS, hsym, hr⟩
    obtain ⟨A, hx, hE⟩ := exists_eq_of_ushape hS
    refine ⟨n, A, _, _, hx, fun u v => ?_, hr.mono fun u v h => (hE u v).mp h⟩
    have e1 := hE u v
    have e2 := hE v u
    have := hsym u v u.isLt v.isLt
    simp only [inEdge] at e1 e2
    cases h1 : A u v <;> cases h2 : A v u <;> simp_all

end Complexity
