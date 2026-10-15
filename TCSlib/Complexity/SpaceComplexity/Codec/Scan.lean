/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.List.Zip
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-state scans over chunked words

The logspace checkers of the configuration codec read their code words letter by letter and
keep only finitely much information in the control. This file supplies the two pure
finite-state devices they are built from, as folds over lists:

* the **chunk adaptor** `Complexity.Codec.adStep`: a letter-level automaton that buffers
  `w + 1` letters and then applies a chunk-level step — so a fold over a word made of
  fixed-width chunks is a fold over its chunks (`Complexity.Codec.foldl_adStep_flatten`);
* the **sliding check** `Complexity.Codec.slStep`: reading two streams `u` and `v` in
  lockstep, verify `vⱼ = G (uⱼ₋₁) (uⱼ) (uⱼ₊₁)` for every `j`, with a padding value `e`
  outside both streams — the shape of "one machine step is a local relation between
  neighbouring cells" (`Complexity.Codec.slide_ok_iff`).

Infrastructure for the codec checkers (finite automata in the sense of [Sip13, §1.1]); not a
result of [AB09].

## Main definitions

* `Complexity.Codec.adStep` — the chunk adaptor.
* `Complexity.Codec.slStep` — the sliding check.

## Main results

* `Complexity.Codec.foldl_adStep_flatten` — the adaptor folds chunk by chunk.
* `Complexity.Codec.slide_ok_iff` — the sliding verdict is the local relation.
* `Complexity.Codec.zip_flatten` — zipping block words blockwise.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
* [Sip13] M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013.
  (§1.1: finite automata.)
-/

namespace Complexity.Codec

/-! ## The chunk adaptor -/

section Adaptor

variable {σ α : Type} {w : ℕ}

/-- The state of the chunk adaptor for chunks of `w + 1` letters: the chunk-level state, the
number of letters of the current chunk read so far, and the buffer. -/
abbrev AdSt (σ α : Type) (w : ℕ) := σ × Fin (w + 1) × (Fin (w + 1) → α)

/-- **The chunk adaptor**: store the letter; on the last letter of a chunk, apply the
chunk-level step `δ` to the buffered chunk and start a new chunk. -/
def adStep (δ : σ → List α → σ) (st : AdSt σ α w) (a : α) : AdSt σ α w :=
  if st.2.1.val = w then (δ st.1 (List.ofFn (Function.update st.2.2 st.2.1 a)), 0,
    Function.update st.2.2 st.2.1 a)
  else (st.1, ⟨(st.2.1.val + 1) % (w + 1), Nat.mod_lt _ (by omega)⟩,
    Function.update st.2.2 st.2.1 a)

/-- Reading a partial chunk only fills the buffer.

**Proof sketch.** Induction on the letters read; each one is stored at the current count,
which then increases, and earlier entries are untouched. -/
lemma foldl_adStep_partial (δ : σ → List α → σ) (s : σ) (l : List α) (j : ℕ)
    (buf : Fin (w + 1) → α) (hj : j + l.length ≤ w) :
    ∃ buf' : Fin (w + 1) → α,
      l.foldl (adStep δ) (s, ⟨j, by omega⟩, buf) = (s, ⟨j + l.length, by omega⟩, buf') ∧
      ∀ t : Fin (w + 1), (hjt : j ≤ t.val) → (htl : t.val < j + l.length) →
        buf' t = l[t.val - j]'(by omega) := by
  induction l generalizing j buf with
  | nil => exact ⟨buf, by simp, fun t h1 h2 => by simp at h2; omega⟩
  | cons a l ih =>
    simp only [List.length_cons] at hj
    have hne : j ≠ w := by omega
    have step : adStep δ (s, ⟨j, by omega⟩, buf) a =
        (s, ⟨j + 1, by omega⟩, Function.update buf ⟨j, by omega⟩ a) := by
      simp only [adStep, hne, ↓reduceIte, Prod.mk.injEq, true_and, and_true]
      exact Fin.ext (Nat.mod_eq_of_lt (by omega))
    obtain ⟨buf', e, hb⟩ := ih (j + 1) (Function.update buf ⟨j, by omega⟩ a) (by omega)
    refine ⟨buf', ?_, ?_⟩
    · rw [List.foldl_cons, step, e]
      simp only [List.length_cons, Prod.mk.injEq, true_and, and_true]
      exact Fin.ext (by simp; omega)
    · intro t h1 h2
      simp only [List.length_cons] at h2
      by_cases ht : t.val = j
      · -- `t` was written by the first letter and is not touched afterwards
        have hfix : ∀ (l' : List α) (j' : ℕ) (b : Fin (w + 1) → α) (hj' : j' + l'.length ≤ w),
            j < j' → (l'.foldl (adStep δ) (s, ⟨j', by omega⟩, b)).2.2 ⟨j, by omega⟩ =
              b ⟨j, by omega⟩ := by
          intro l'
          induction l' with
          | nil => intros; rfl
          | cons a' l' ih' =>
            intro j' b hj' hjj
            simp only [List.length_cons] at hj'
            have hne' : j' ≠ w := by omega
            rw [List.foldl_cons]
            have st' : adStep δ (s, ⟨j', by omega⟩, b) a' =
                (s, ⟨j' + 1, by omega⟩, Function.update b ⟨j', by omega⟩ a') := by
              simp only [adStep, hne', ↓reduceIte, Prod.mk.injEq, true_and, and_true]
              exact Fin.ext (Nat.mod_eq_of_lt (by omega))
            rw [st', ih' (j' + 1) _ (by omega) (by omega)]
            rw [Function.update_of_ne (by simp [Fin.ext_iff]; omega)]
        have := hfix l (j + 1) (Function.update buf ⟨j, by omega⟩ a) (by omega) (by omega)
        rw [e] at this
        simp only at this
        have hbt : buf' t = a := by
          have tj : t = ⟨j, by omega⟩ := Fin.ext ht
          rw [tj]; simpa using this
        rw [hbt]
        simp only [ht, Nat.sub_self, List.getElem_cons_zero]
      · rw [hb t (by omega) (by omega)]
        have : t.val - j = (t.val - (j + 1)) + 1 := by omega
        simp only [this, List.getElem_cons_succ]

/-- One chunk of `w + 1` letters through the adaptor is one chunk-level step.

**Proof sketch.** Split the chunk into its first `w` letters and its last letter. The
partial lemma fills the buffer with the first `w`; the last letter completes the buffer,
which then lists exactly the chunk, and `δ` is applied. -/
lemma foldl_adStep_chunk (δ : σ → List α → σ) (s : σ) (ch : List α)
    (hch : ch.length = w + 1) (buf : Fin (w + 1) → α) :
    ∃ buf' : Fin (w + 1) → α, ch.foldl (adStep δ) (s, 0, buf) = (δ s ch, 0, buf') := by
  obtain ⟨l, a, rfl⟩ : ∃ l a, ch = l ++ [a] := by
    rcases List.eq_nil_or_concat ch with h | ⟨l, a, h⟩
    · subst h; simp at hch
    · exact ⟨l, a, by rw [h, List.concat_eq_append]⟩
  simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hch
  obtain ⟨b, e, hb⟩ := foldl_adStep_partial δ s l 0 buf (by omega)
  refine ⟨Function.update b ⟨w, by omega⟩ a, ?_⟩
  rw [List.foldl_append, show ((0 : Fin (w + 1))) = ⟨0, by omega⟩ from rfl, e]
  simp only [List.foldl_cons, List.foldl_nil, adStep, Nat.zero_add, hch, ↓reduceIte]
  have hof : List.ofFn (Function.update b ⟨w, by omega⟩ a) = l ++ [a] := by
    apply List.ext_getElem (by simp; omega)
    intro t h1 h2
    simp only [List.length_ofFn] at h1
    simp only [List.getElem_ofFn]
    by_cases ht : t = w
    · have hw : (⟨t, h1⟩ : Fin (w + 1)) = ⟨w, by omega⟩ := Fin.ext ht
      rw [hw, Function.update_self, List.getElem_append_right (by omega)]
      simp [ht, hch]
    · have hne : (⟨t, h1⟩ : Fin (w + 1)) ≠ ⟨w, by omega⟩ := fun h => ht (congrArg Fin.val h)
      rw [Function.update_of_ne hne, hb ⟨t, h1⟩ (Nat.zero_le _) (by simp; omega),
        List.getElem_append_left (by omega)]
      simp
  rw [hof]
  rfl

/-- **The adaptor folds chunk by chunk**: on a word that is a concatenation of chunks of
`w + 1` letters, the adaptor started at a chunk boundary ends at a chunk boundary with the
chunk-level fold.

**Proof sketch.** Induction on the chunks, one `foldl_adStep_chunk` per chunk. -/
theorem foldl_adStep_flatten (δ : σ → List α → σ) (s : σ) (L : List (List α))
    (hL : ∀ ch ∈ L, ch.length = w + 1) (buf : Fin (w + 1) → α) :
    ∃ buf' : Fin (w + 1) → α, L.flatten.foldl (adStep δ) (s, 0, buf) = (L.foldl δ s, 0, buf') := by
  induction L generalizing s buf with
  | nil => exact ⟨buf, rfl⟩
  | cons ch L ih =>
    obtain ⟨b, e⟩ := foldl_adStep_chunk δ s ch (hL ch (by simp)) buf
    obtain ⟨b', e'⟩ := ih (δ s ch) (fun c hc => hL c (by simp [hc])) b
    exact ⟨b', by rw [List.flatten_cons, List.foldl_append, e, e', List.foldl_cons]⟩

end Adaptor

/-! ## Zipping block words -/

/-- Zipping two concatenations of blocks of matching lengths is concatenating the blockwise
zips. -/
theorem zip_flatten {α β : Type} (L₁ : List (List α)) (L₂ : List (List β))
    (h : L₁.length = L₂.length)
    (hl : ∀ (i : ℕ) (h₁ : i < L₁.length) (h₂ : i < L₂.length), L₁[i].length = L₂[i].length) :
    List.zip L₁.flatten L₂.flatten = (List.zipWith List.zip L₁ L₂).flatten := by
  induction L₁ generalizing L₂ with
  | nil => simp
  | cons a L₁ ih =>
    cases L₂ with
    | nil => simp at h
    | cons b L₂ =>
      simp only [List.flatten_cons, List.zipWith_cons_cons]
      have h0 := hl 0 (by simp) (by simp)
      simp only [List.getElem_cons_zero] at h0
      rw [List.zip_append h0,
        ih L₂ (by simpa using h) (fun i h₁ h₂ => hl (i + 1) (by simpa using h₁)
          (by simpa using h₂))]

/-! ## The sliding check -/

section Slide

variable {X : Type} [DecidableEq X]

/-- The state of the sliding check: the two previous letters of the first stream, the
previous letter of the second stream, and the verdict so far. -/
abbrev SlSt (X : Type) := X × X × X × Bool

/-- **The sliding check**: on reading `(uⱼ, vⱼ)`, verify `vⱼ₋₁ = G uⱼ₋₂ uⱼ₋₁ uⱼ` and shift. -/
def slStep (G : X → X → X → X) (st : SlSt X) (uv : X × X) : SlSt X :=
  (st.2.1, uv.1, uv.2, st.2.2.2 && decide (st.2.2.1 = G st.1 st.2.1 uv.1))

/-- The sliding check on index sequences, in closed form: after `J` pairs the state holds the
last two first-stream letters and the last second-stream letter (padded by `e` before the
start), and the verdict is the local relation at every earlier position.

**Proof sketch.** Induction on `J` (`List.range_succ`, `List.foldl_append`). -/
lemma foldl_slStep_range (G : X → X → X → X) (e : X) (f g : ℕ → X) (J : ℕ) :
    ((List.range J).map (fun i => (f i, g i))).foldl (slStep G) (e, e, e, true) =
      ((e :: e :: (List.range J).map f).getD J e,
        (e :: e :: (List.range J).map f).getD (J + 1) e,
        (e :: (List.range J).map g).getD J e,
        decide (∀ i < J, (e :: (List.range J).map g).getD i e =
          G ((e :: e :: (List.range J).map f).getD i e)
            ((e :: e :: (List.range J).map f).getD (i + 1) e)
            ((e :: e :: (List.range J).map f).getD (i + 2) e))) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [List.range_succ, List.map_append, List.foldl_append, ih]
    simp only [List.map_append, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
      slStep]
    have get1 : ∀ i, i < J + 2 → (e :: e :: ((List.range J).map f ++ [f J])).getD i e =
        (e :: e :: (List.range J).map f).getD i e := by
      intro i hi
      simp only [List.getD_eq_getElem?_getD]
      rcases i with _ | _ | i
      · rfl
      · rfl
      · simp only [List.getElem?_cons_succ]
        rw [List.getElem?_append_left (by simp; omega)]
    have get2 : ∀ i, i < J + 1 → (e :: ((List.range J).map g ++ [g J])).getD i e =
        (e :: (List.range J).map g).getD i e := by
      intro i hi
      simp only [List.getD_eq_getElem?_getD]
      rcases i with _ | i
      · rfl
      · simp only [List.getElem?_cons_succ]
        rw [List.getElem?_append_left (by simp; omega)]
    have lastf : (e :: e :: ((List.range J).map f ++ [f J])).getD (J + 2) e = f J := by
      simp [List.getD_eq_getElem?_getD]
    have lastg : (e :: ((List.range J).map g ++ [g J])).getD (J + 1) e = g J := by
      simp [List.getD_eq_getElem?_getD]
    have beyondf : (e :: e :: (List.range J).map f).getD (J + 2) e = e := by
      simp [List.getD_eq_getElem?_getD]
    simp only [Prod.mk.injEq]
    refine ⟨(get1 (J + 1) (by omega)).symm, lastf.symm, lastg.symm, ?_⟩
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hall, hlast⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [get2 i (by omega), get1 i (by omega), get1 (i + 1) (by omega),
          get1 (i + 2) (by omega)]
        exact hall i hi
      · rw [get2 i (by omega), get1 i (by omega), get1 (i + 1) (by omega), lastf]
        exact hlast
    · intro hall
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hall i (by omega)
        rwa [get2 i (by omega), get1 i (by omega), get1 (i + 1) (by omega),
          get1 (i + 2) (by omega)] at this
      · have := hall J (by omega)
        rwa [get2 J (by omega), get1 J (by omega), get1 (J + 1) (by omega), lastf] at this

/-- **The sliding verdict is the local relation**: on two streams `u`, `v` of equal length
`m`, followed by two padding pairs `(e, e)`, the sliding check accepts iff for every
`j < m + 2`, `vⱼ₋₁ = G uⱼ₋₂ uⱼ₋₁ uⱼ` (all letters outside the streams read as `e`) — i.e.
`v` is the image of `u` under the local rule `G`, and `G` maps the padding next to either
end of `u` to `e`.

**Proof sketch.** Rewrite the input as the indexed sequence `j ↦ (uⱼ, vⱼ)` for `j < m + 2`
(padded by `e`) and apply the closed form `foldl_slStep_range`; for `j ≤ m + 1` the padded
prefixes agree with the padded streams. -/
theorem slide_ok_iff (G : X → X → X → X) (e : X) (u v : List X) (h : u.length = v.length) :
    ((List.zip u v ++ [(e, e), (e, e)]).foldl (slStep G) (e, e, e, true)).2.2.2 = true ↔
      ∀ i < u.length + 2, (e :: v).getD i e =
        G ((e :: e :: u).getD i e) ((e :: e :: u).getD (i + 1) e)
          ((e :: e :: u).getD (i + 2) e) := by
  have hin : List.zip u v ++ [(e, e), (e, e)] =
      (List.range (u.length + 2)).map (fun i => (u.getD i e, v.getD i e)) := by
    apply List.ext_getElem (by simp [h])
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
    by_cases hi : i < u.length
    · rw [List.getElem_append_left (by simp [h]; omega)]
      simp [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (h ▸ hi : i < v.length)]
    · rw [List.getElem_append_right (by simp [h]; omega)]
      simp only [List.length_zip, h, min_self, List.length_append, List.length_cons,
        List.length_nil] at h1 ⊢
      have hu : u[i]? = none := List.getElem?_eq_none (by omega)
      have hv : v[i]? = none := List.getElem?_eq_none (by omega)
      rw [hu, hv]
      rcases (show i - v.length = 0 ∨ i - v.length = 1 by omega) with e1 | e1 <;> simp [e1]
  rw [hin, foldl_slStep_range]
  simp only [decide_eq_true_eq]
  have fu : ∀ i, i ≤ u.length + 3 → (e :: e :: (List.range (u.length + 2)).map
      (fun i => u.getD i e)).getD i e = (e :: e :: u).getD i e := by
    intro i _
    simp only [List.getD_eq_getElem?_getD]
    rcases i with _ | _ | i
    · rfl
    · rfl
    · by_cases hi : i < u.length + 2
      · simp [hi]
      · simp [hi, List.getElem?_eq_none (show u.length ≤ i by omega)]
  have fv : ∀ i, (e :: (List.range (u.length + 2)).map (fun i => v.getD i e)).getD i e =
      (e :: v).getD i e := by
    intro i
    simp only [List.getD_eq_getElem?_getD]
    rcases i with _ | i
    · rfl
    · by_cases hi : i < u.length + 2
      · simp [hi]
      · simp [hi, List.getElem?_eq_none (show v.length ≤ i by omega)]
  constructor
  · intro hall i hi
    have := hall i hi
    rwa [fv, fu i (by omega), fu (i + 1) (by omega), fu (i + 2) (by omega)] at this
  · intro hall i hi
    rw [fv, fu i (by omega), fu (i + 1) (by omega), fu (i + 2) (by omega)]
    exact hall i hi

end Slide

end Complexity.Codec
