/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.OracleAdversary
import Mathlib.Data.Fintype.Pi

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Lazy sampling of a random oracle

A random function `R : I → O` has `|O|^|I|` values, far too many for an efficient
reduction to sample. An oracle algorithm making at most `q` queries only ever looks at
`q` of them, and the standard remedy [Gar26, footnote 9 of §3.4] is *lazy sampling*: keep
a list of the distinct queries seen so far, answer a repeated query consistently, and
answer the `k`-th new query with a fresh value `W k`. This file proves that lazy
sampling with `q` uniform values `W : Fin q → O` produces exactly the same output
distribution as a uniform random function.

The lazy run is stated for an arbitrary answer stream `a : ℕ → O` (the answer to the
`k`-th distinct query is `a k`), so that hybrids can mix fresh values with other
answers index by index.

## Main definitions

* `QueryTree.noteQuery L x`: the list of distinct queries after querying `x`.
* `QueryTree.evalLazy a t L`: run `t`, answering the `k`-th distinct query by `a k`.
* `extendStream W`: a finite list of values `W : Fin q → O` as an answer stream.

## Main results

* `QueryTree.evalLazy_congr`: a run making at most `m` more queries only reads the first
  `L.length + m` entries of the answer stream.
* `QueryTree.uprob_evalLazy`: lazy sampling with `q` uniform fresh values has the same
  output distribution as a uniform random function, for trees making at most `q`
  queries.
* Probability helpers: `uprob_congr`, `uprob_prod_comm`, `uprob_snd`,
  `uprob_sections_congr`, `uprob_update_absorb`, `uprob_update_split`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, footnote 9 (lazy sampling of random functions).
-/

namespace TCSlib.Cryptography

open Function

section Helpers

variable {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]

/-- Events that are equivalent pointwise have the same probability. -/
theorem uprob_congr {p p' : α → Prop} (h : ∀ a, p a ↔ p' a) : uprob p = uprob p' :=
  congrArg uprob (funext fun a => propext (h a))

/-- Swapping the two coordinates of a product does not change probabilities. -/
theorem uprob_prod_comm (p : α → β → Prop) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : β × α => p z.2 z.1) :=
  (uprob_comp_equiv (Equiv.prodComm β α) (fun z : α × β => p z.1 z.2)).symm

/-- An event depending only on the second coordinate has the same probability on the
product. -/
theorem uprob_snd [Nonempty α] (p : β → Prop) :
    uprob (fun z : α × β => p z.2) = uprob p := by
  rw [uprob_prod_comm (fun _ b => p b)]
  exact uprob_fst p

/-- Two events on products with the same first factor have the same probability when
every section has the same probability. -/
theorem uprob_sections_congr (p : α → β → Prop) (p' : α → γ → Prop)
    (h : ∀ a, uprob (p a) = uprob (p' a)) :
    uprob (fun z : α × β => p z.1 z.2) = uprob (fun z : α × γ => p' z.1 z.2) := by
  rw [uprob_prod, uprob_prod]
  exact congrArg uexp (funext h)

variable [DecidableEq α]

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform: the overwritten entry is absorbed. -/
theorem uprob_update_absorb [Nonempty β] (i : α) (f : (α → β) → γ → Prop) :
    uprob (fun z : β × ((α → β) × γ) => f (update z.2.1 i z.1) z.2.2) =
      uprob (fun z : (α → β) × γ => f z.1 z.2) := by
  let e : β × ((α → β) × γ) ≃ ((α → β) × γ) × β :=
    { toFun := fun z => ((update z.2.1 i z.1, z.2.2), z.2.1 i)
      invFun := fun w => (w.1.1 i, (update w.1.1 i w.2, w.1.2))
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1.1 w.1.2)).trans
    (uprob_fst (fun w : (α → β) × γ => f w.1 w.2))

/-- Overwriting one entry of a uniform table by an independent uniform value leaves the
table uniform (version without extra coordinates). -/
theorem uprob_update_absorb' [Nonempty β] (i : α) (f : (α → β) → Prop) :
    uprob (fun z : β × (α → β) => f (update z.2 i z.1)) = uprob f := by
  let e : β × (α → β) ≃ (α → β) × β :=
    { toFun := fun z => (update z.2 i z.1, z.2 i)
      invFun := fun w => (w.1 i, update w.1 i w.2)
      left_inv := fun z => by simp
      right_inv := fun w => by simp }
  exact (uprob_comp_equiv e (fun w => f w.1)).trans (uprob_fst f)

/-- If an event on a uniform table `W` depends on the entry `W i` only through a
parameter `v` (it does not otherwise read position `i`), its probability is the average
over `v` of the probability with `v` fixed. -/
theorem uprob_update_split [Nonempty β] (i : α) (g : β → (α → β) → Prop)
    (hg : ∀ v W u, g v (update W i u) ↔ g v W) :
    uprob (fun W => g (W i) W) = uexp (fun v => uprob (fun W => g v W)) := by
  rw [← uprob_prod (fun z : β × (α → β) => g z.1 z.2),
    ← uprob_update_absorb' i (fun W => g (W i) W)]
  exact uprob_congr fun z => by simp [hg]

end Helpers

namespace QueryTree

variable {I : Type*} {O : Type*} {α : Type*} [DecidableEq I]

/-- The list of distinct queries after the query `x`, given the list `L` of distinct
queries so far: `x` is appended if it is new. -/
def noteQuery (L : List I) (x : I) : List I := if x ∈ L then L else L ++ [x]

/-- A repeated query leaves the list of distinct queries unchanged. -/
theorem noteQuery_of_mem {L : List I} {x : I} (h : x ∈ L) : noteQuery L x = L := if_pos h

/-- A new query is appended to the list of distinct queries. -/
theorem noteQuery_of_not_mem {L : List I} {x : I} (h : x ∉ L) : noteQuery L x = L ++ [x] :=
  if_neg h

/-- The index of the current query in the updated list is below its length. -/
theorem idxOf_noteQuery_lt (L : List I) (x : I) :
    (noteQuery L x).idxOf x < (noteQuery L x).length := by
  rw [List.idxOf_lt_length_iff]
  unfold noteQuery; split_ifs with h <;> simp [h]

/-- Querying adds at most one entry to the list of distinct queries. -/
theorem length_noteQuery_le (L : List I) (x : I) :
    (noteQuery L x).length ≤ L.length + 1 := by
  unfold noteQuery; split_ifs <;> simp

/-- Run `t` against a lazily sampled oracle: with `L` the list of distinct queries so
far, the query `x` is answered by `a k`, where `k` is the position of `x` among the
distinct queries in order of first appearance. A repeated query gets the same answer as
before. [Gar26, §3.4.2, footnote 9]. -/
def evalLazy (a : ℕ → O) : QueryTree I O α → List I → α
  | ret y, _ => y
  | query x k, L =>
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x)

/-- A leaf returns its output whatever the answers. -/
@[simp] theorem evalLazy_ret (a : ℕ → O) (y : α) (L : List I) :
    evalLazy a (ret y) L = y := rfl

/-- A query is recorded and answered by the stream entry at its position. -/
theorem evalLazy_query (a : ℕ → O) (x : I) (k : O → QueryTree I O α) (L : List I) :
    evalLazy a (query x k) L =
      evalLazy a (k (a ((noteQuery L x).idxOf x))) (noteQuery L x) := rfl

/-- A run making at most `m` further queries, started with `L` distinct queries already
seen, only reads the answer stream below `L.length + m`. -/
theorem evalLazy_congr {a b : ℕ → O} {t : QueryTree I O α} {m : ℕ} (ht : t.BoundedBy m)
    (L : List I) (hab : ∀ k < L.length + m, a k = b k) :
    evalLazy a t L = evalLazy b t L := by
  induction t generalizing m L with
  | ret y => rfl
  | query x k ih =>
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
      have h1 := idxOf_noteQuery_lt L x
      have h2 := length_noteQuery_le L x
      rw [evalLazy_query, evalLazy_query, hab _ (by omega)]
      exact ih _ (ht _) _ fun j hj => hab j (by omega)

/-- Post-processing every lazy answer by `g` is the same as running the tree whose
answers are post-processed by `g`. -/
theorem evalLazy_comp {O' : Type*} (g : O' → O) (a : ℕ → O') (t : QueryTree I O α)
    (L : List I) :
    evalLazy (g ∘ a) t L = evalLazy a (t.simulate id (fun _ => g)) L := by
  induction t generalizing L with
  | ret y => rfl
  | query x k ih => exact ih _ _

end QueryTree

/-- A finite list `W : Fin q → O` of values as an answer stream; entries beyond `q` are
an arbitrary fixed value and are never read by trees making at most `q` queries. -/
noncomputable def extendStream {O : Type*} [Nonempty O] {q : ℕ} (W : Fin q → O) : ℕ → O :=
  fun k => if h : k < q then W ⟨k, h⟩ else Classical.arbitrary O

namespace QueryTree

variable {I : Type*} {O : Type*} {α : Type*} [DecidableEq I]

/-- A constant event has the same probability on any two nonempty finite types. -/
private theorem uprob_const_eq {β γ : Type*} [Fintype β] [Fintype γ] [Nonempty β]
    [Nonempty γ] (P : Prop) : uprob (fun _ : β => P) = uprob (fun _ : γ => P) := by
  by_cases h : P
  · rw [uprob_congr (p' := fun _ : β => True) (fun _ => iff_true_intro h),
      uprob_congr (p' := fun _ : γ => True) (fun _ => iff_true_intro h), uprob_true,
      uprob_true]
  · rw [uprob_congr (p' := fun _ : β => False) (fun _ => iff_false_intro h),
      uprob_congr (p' := fun _ : γ => False) (fun _ => iff_false_intro h), uprob_false,
      uprob_false]

/-- Keep the first `ℓ` entries of `W₀` and take the remaining entries from `W`. -/
private def combine {q : ℕ} (ℓ : ℕ) (W₀ W : Fin q → O) : Fin q → O :=
  fun i => if i.val < ℓ then W₀ i else W i

/-- The table answering a recorded query `x ∈ L` from the stream `a` at the position of `x`
in `L`, and every other query from `R`. -/
private def mergeTable (L : List I) (a : ℕ → O) (R : I → O) : I → O :=
  fun x => if x ∈ L then a (L.idxOf x) else R x

section Streams

variable [Nonempty O] {q : ℕ}

/-- Overwriting entry `j` of a value list does not change the stream at other positions. -/
theorem extendStream_update_of_ne (W : Fin q → O) (j : Fin q) (v : O) {k : ℕ}
    (hk : k ≠ j.val) : extendStream (update W j v) k = extendStream W k := by
  unfold extendStream
  split_ifs with h
  · exact update_of_ne (fun e => hk (by rw [← e])) _ _
  · rfl

/-- Overwriting entry `j` of a value list by `v` makes the stream read `v` at `j`. -/
theorem extendStream_update_self (W : Fin q → O) (j : Fin q) (v : O) :
    extendStream (update W j v) j.val = v := by
  simp [extendStream]

private theorem extendStream_combine_of_lt (W₀ W : Fin q → O) {ℓ k : ℕ} (hk : k < ℓ) :
    extendStream (combine ℓ W₀ W) k = extendStream W₀ k := by
  unfold extendStream combine
  split_ifs <;> simp_all

private theorem extendStream_combine_self (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    extendStream (combine ℓ W₀ W) ℓ = W ⟨ℓ, hℓ⟩ := by
  simp [extendStream, combine, hℓ]

omit [Nonempty O] in
private theorem combine_succ (W₀ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) :
    combine ℓ W₀ W = combine (ℓ + 1) (update W₀ ⟨ℓ, hℓ⟩ (W ⟨ℓ, hℓ⟩)) W := by
  funext i
  unfold combine
  by_cases h1 : i.val < ℓ
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h1; exact lt_irrefl _ h1
    simp [h1, Nat.lt_succ_of_lt h1, this]
  · by_cases h2 : i.val = ℓ
    · have : i = ⟨ℓ, hℓ⟩ := Fin.ext h2
      subst this; simp
    · have : ¬ i.val < ℓ + 1 := by omega
      simp [h1, this]

omit [Nonempty O] in
private theorem combine_update (W₁ W : Fin q → O) {ℓ : ℕ} (hℓ : ℓ < q) (u : O) :
    combine (ℓ + 1) W₁ (update W ⟨ℓ, hℓ⟩ u) = combine (ℓ + 1) W₁ W := by
  funext i
  unfold combine
  by_cases h : i.val < ℓ + 1
  · simp [h]
  · have : i ≠ ⟨ℓ, hℓ⟩ := fun e => by rw [e] at h; exact h (Nat.lt_succ_self _)
    simp [h, this]

private theorem mergeTable_append (W₀ : Fin q → O) (R : I → O) {L : List I} {x : I}
    (hx : x ∉ L) (hℓ : L.length < q) :
    mergeTable L (extendStream W₀) R =
      mergeTable (L ++ [x]) (extendStream (update W₀ ⟨L.length, hℓ⟩ (R x))) R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · have hlt := List.idxOf_lt_length_of_mem hy
    rw [if_pos hy, if_pos (List.mem_append_left _ hy), List.idxOf_append_of_mem hy,
      extendStream_update_of_ne _ _ _ (by simp; omega)]
  · by_cases hyx : y = x
    · subst hyx
      rw [if_neg hy, if_pos (by simp), List.idxOf_append_of_notMem hy]
      simpa using (extendStream_update_self W₀ ⟨L.length, hℓ⟩ (R y)).symm
    · rw [if_neg hy, if_neg (by simp [hy, hyx])]

omit [Nonempty O] in
private theorem mergeTable_update (L : List I) (a : ℕ → O) (R : I → O) {x : I} (hx : x ∈ L)
    (u : O) : mergeTable L a (update R x u) = mergeTable L a R := by
  funext y
  unfold mergeTable
  by_cases hy : y ∈ L
  · simp [hy]
  · have : y ≠ x := fun e => hy (e ▸ hx)
    simp [hy, this]

end Streams

/-- The generalized lazy-sampling invariant: started with `L` already recorded, with
answers `W₀` on `L`, the lazy run with fresh values beyond `L` and the run against a
random function agreeing with `W₀` on `L` have the same output distribution.

**Proof sketch.** Induction on the tree. A repeated query is answered by the recorded
value on both sides. For a new query `x`, the lazy side answers with the fresh entry at
position `|L|` and the table side with `R x`; record this answer `v` in `W₀`. Neither
continuation reads the entry again, so both probabilities are averages over `v` of the
continuation probabilities (`uprob_update_split`), which agree by induction. -/
private theorem uprob_evalLazy_aux [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {q : ℕ} (t : QueryTree I O α) : ∀ (m : ℕ) (L : List I) (W₀ : Fin q → O),
    t.BoundedBy m → L.length + m ≤ q →
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream (combine L.length W₀ W)) t L)) =
      uprob (fun R : I → O => φ (t.eval (mergeTable L (extendStream W₀) R))) := by
  induction t with
  | ret y => intro _ _ _ _ _; exact uprob_const_eq (β := Fin q → O) (γ := I → O) (φ y)
  | query x k ih =>
    intro m L W₀ ht hm
    cases m with
    | zero => exact absurd ht (boundedBy_query_zero x k)
    | succ m =>
    by_cases hx : x ∈ L
    · -- a repeated query: both sides answer with the recorded value
      have hi : L.idxOf x < L.length := List.idxOf_lt_length_of_mem hx
      have hl : ∀ W, evalLazy (extendStream (combine L.length W₀ W)) (query x k) L =
          evalLazy (extendStream (combine L.length W₀ W)) (k (extendStream W₀ (L.idxOf x)))
            L := by
        intro W
        rw [evalLazy_query, noteQuery_of_mem hx, extendStream_combine_of_lt _ _ hi]
      have hr : ∀ R, (query x k).eval (mergeTable L (extendStream W₀) R) =
          (k (extendStream W₀ (L.idxOf x))).eval (mergeTable L (extendStream W₀) R) := by
        intro R; simp [mergeTable, hx]
      simp only [hl, hr]
      exact ih _ m L W₀ (ht _) (by omega)
    · -- a new query: split off the fresh value on both sides
      have hℓ : L.length < q := by omega
      have hidx : (L ++ [x]).idxOf x = L.length := by
        rw [List.idxOf_append_of_notMem hx]; simp
      have hlen : (L ++ [x]).length = L.length + 1 := by simp
      let j : Fin q := ⟨L.length, hℓ⟩
      let g : O → (Fin q → O) → Prop := fun v W =>
        φ (evalLazy (extendStream (combine (L ++ [x]).length (update W₀ j v) W)) (k v)
          (L ++ [x]))
      let h : O → (I → O) → Prop := fun v R =>
        φ ((k v).eval (mergeTable (L ++ [x]) (extendStream (update W₀ j v)) R))
      have hl : ∀ W, φ (evalLazy (extendStream (combine L.length W₀ W)) (query x k) L) ↔
          g (W j) W := by
        intro W
        simp only [g, evalLazy_query, noteQuery_of_not_mem hx, hidx, hlen,
          extendStream_combine_self _ _ hℓ, ← combine_succ _ _ hℓ, j]
      have hr : ∀ R, φ ((query x k).eval (mergeTable L (extendStream W₀) R)) ↔
          h (R x) R := by
        intro R
        simp only [h, eval_query, ← mergeTable_append W₀ R hx hℓ, j]
        simp [mergeTable, hx]
      rw [uprob_congr hl, uprob_congr hr,
        uprob_update_split j g (fun v W u => by simp only [g, hlen, j, combine_update]),
        uprob_update_split x h (fun v R u => by
          simp only [h, mergeTable_update _ _ _ (List.mem_append_right L
            (List.mem_singleton_self x))])]
      exact congrArg uexp (funext fun v =>
        ih v m (L ++ [x]) (update W₀ j v) (ht v) (by rw [hlen]; omega))

/-- **Lazy sampling.** For a query tree making at most `q` queries, answering the `k`-th
distinct query by the `k`-th of `q` independent uniform values gives the same output
distribution as answering by a uniform random function. [Gar26, §3.4.2, footnote 9],
stated as an exact equality of probabilities for every event on the output.

**Proof sketch.** Generalize to a run started with a list `L` of `ℓ` distinct queries
whose answers are fixed values `W₀`, against a random function that agrees with `W₀` on
`L`. A repeated query is answered by the fixed value on both sides. A new query is
answered by the fresh value `W ℓ` on the lazy side and by `R x` on the table side; in
both cases the rest of the run does not read this entry again except through the
recorded answer, so both probabilities are the average over the answer `v` of the
probability of the continuation with `v` recorded, which agree by induction. -/
theorem uprob_evalLazy [Fintype I] [Fintype O] [Nonempty O] (φ : α → Prop)
    {t : QueryTree I O α} {q : ℕ} (ht : t.BoundedBy q) :
    uprob (fun W : Fin q → O => φ (evalLazy (extendStream W) t [])) =
      uprob (fun R : I → O => φ (t.eval R)) := by
  have h := uprob_evalLazy_aux (q := q) φ t q [] (fun _ => Classical.arbitrary O) ht (by simp)
  have h1 : ∀ W : Fin q → O, combine ([] : List I).length (fun _ => Classical.arbitrary O) W = W :=
    fun W => funext fun i => by simp [combine]
  have h2 : ∀ R : I → O, mergeTable [] (extendStream fun _ : Fin q => Classical.arbitrary O)
      R = R := fun R => funext fun y => by simp [mergeTable]
  simpa only [h1, h2] using h

end QueryTree

end TCSlib.Cryptography
