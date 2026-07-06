/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic
import TCSlib.CommunicationComplexity.DeterministicCC.Trees
import Mathlib.Data.Set.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Subprotocol Embedding

## Main results

- `Deterministic.Protocol.IsSubprotocol`: Inductive predicate asserting that one protocol is a rooted subtree of another
- `Deterministic.Protocol.balanced_subprotocol`: Every protocol with more than one leaf has a subprotocol with a balanced (⅓–⅔) fraction of its leaves
- `Deterministic.Protocol.testSubprotocol`: A two-bit test protocol that routes inputs to one of two sub-protocols based on whether they reach a given subprotocol

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- `IsSubprotocol s p` means `s` is a (rooted) subtree of protocol `p`. -/
inductive IsSubprotocol : Protocol X Y α → Protocol X Y α → Prop where
| refl : ∀ p, IsSubprotocol p p
| alice_false : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.alice f P)
| alice_true  : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.alice f P)
| bob_false   : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.bob f P)
| bob_true    : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.bob f P)

/-- Transitivity of subprotocol embeddings. -/
lemma IsSubprotocol.trans
    {s t u : Protocol X Y α}
    (h1 : IsSubprotocol s t) (h2 : IsSubprotocol t u) : IsSubprotocol s u := by
  induction h2 with
  | refl _ => exact h1
  | alice_false f P t ht ih => exact IsSubprotocol.alice_false f P s (ih h1)
  | alice_true f P t ht ih => exact IsSubprotocol.alice_true f P s (ih h1)
  | bob_false f P t ht ih => exact IsSubprotocol.bob_false f P s (ih h1)
  | bob_true f P t ht ih => exact IsSubprotocol.bob_true f P s (ih h1)

private lemma balanced_aux (p : Protocol X Y α) (n : ℕ) (hn : 1 < n)
    (h : 3 * p.numLeaves ≥ 2 * n) :
    ∃ s : Protocol X Y α,
      IsSubprotocol s p ∧ 3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction p with
  | output v =>
    simp [numLeaves, shape] at h
    omega
  | alice f P ih =>
    have hsum : (Protocol.alice f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [numLeaves, shape]
    have htot : 3 * ((P false).numLeaves + (P true).numLeaves) ≥ 2 * n := by
      simpa [hsum] using h
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * n
      · refine ⟨P false, IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P false).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih false hchild
        exact ⟨s,
          hs.trans (IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _)), hs1, hs2⟩
    · by_cases hlt : 3 * (P true).numLeaves < 2 * n
      · refine ⟨P true, IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P true).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih true hchild
        exact ⟨s, hs.trans (IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _)), hs1, hs2⟩
  | bob f P ih =>
    have hsum : (Protocol.bob f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [numLeaves, shape]
    have htot : 3 * ((P false).numLeaves + (P true).numLeaves) ≥ 2 * n := by
      simpa [hsum] using h
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * n
      · refine ⟨P false, IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P false).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih false hchild
        exact ⟨s, hs.trans (IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _)), hs1, hs2⟩
    · by_cases hlt : 3 * (P true).numLeaves < 2 * n
      · refine ⟨P true, IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _), ?_, hlt⟩
        omega
      · have hchild : 3 * (P true).numLeaves ≥ 2 * n := by omega
        obtain ⟨s, hs, hs1, hs2⟩ := ih true hchild
        exact ⟨s, hs.trans (IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _)), hs1, hs2⟩

/-- If a protocol has more than one leaf, it has a subprotocol with a balanced number of leaves. -/
theorem balanced_subprotocol (p : Protocol X Y α) (hn : 1 < p.numLeaves) :
    ∃ s : Protocol X Y α,
      IsSubprotocol s p ∧ 3 * s.numLeaves ≥ p.numLeaves ∧
      3 * s.numLeaves < 2 * p.numLeaves := by
  induction p with
  | output v =>
    simp [numLeaves, shape] at hn
  | alice f P ih =>
    have hsum : (Protocol.alice f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [numLeaves, shape]
    have hn' : 1 < (P false).numLeaves + (P true).numLeaves := by
      simpa [hsum] using hn
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P false, IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using
            (show 3 * (P false).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P false) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.alice_false f P (P false) (IsSubprotocol.refl _)),
          hs1, ?_⟩
        simpa [hsum] using hs2
    · by_cases hlt : 3 * (P true).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P true, IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using
            (show 3 * (P true).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P true) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.alice_true f P (P true) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2
  | bob f P ih =>
    have hsum : (Protocol.bob f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [numLeaves, shape]
    have hn' : 1 < (P false).numLeaves + (P true).numLeaves := by
      simpa [hsum] using hn
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · by_cases hlt : 3 * (P false).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P false, IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using
            (show 3 * (P false).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P false) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.bob_false f P (P false) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2
    · by_cases hlt : 3 * (P true).numLeaves < 2 * ((P false).numLeaves + (P true).numLeaves)
      · refine ⟨P true, IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _), ?_, ?_⟩
        · simpa [hsum] using
            (show 3 * (P true).numLeaves ≥ (P false).numLeaves + (P true).numLeaves by omega)
        · simpa [hsum] using hlt
      · obtain ⟨s, hs, hs1, hs2⟩ :=
          balanced_aux (P true) ((P false).numLeaves + (P true).numLeaves) hn' (by omega)
        refine ⟨s, hs.trans (IsSubprotocol.bob_true f P (P true) (IsSubprotocol.refl _)), hs1, ?_⟩
        simpa [hsum] using hs2

/-- Type-valued witness for a subtree embedding, used for data-carrying recursion. It is a
witness that `s` is a subprotocol of `p` containing the choices from the root of `p` to the
root of `s`. -/
inductive SubprotocolPath : Protocol X Y α → Protocol X Y α → Type _ where
| refl : ∀ p, SubprotocolPath p p
| alice_false : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.alice f P)
| alice_true  : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.alice f P)
| bob_false   : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.bob f P)
| bob_true    : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.bob f P)

/-- Every `SubprotocolPath` induces an `IsSubprotocol` proof. -/
def SubprotocolPath.toIsSubprotocol {s p : Protocol X Y α} :
    SubprotocolPath s p → IsSubprotocol s p
  | .refl p => IsSubprotocol.refl p
  | .alice_false f P s hs => IsSubprotocol.alice_false f P s (hs.toIsSubprotocol)
  | .alice_true f P s hs => IsSubprotocol.alice_true f P s (hs.toIsSubprotocol)
  | .bob_false f P s hs => IsSubprotocol.bob_false f P s (hs.toIsSubprotocol)
  | .bob_true f P s hs => IsSubprotocol.bob_true f P s (hs.toIsSubprotocol)

/-- If `s` is a subprotocol of `p`, then there is a path from the root of `p` to the
root of `s`. -/
theorem path_exists_of_isSubprotocol {s p : Protocol X Y α}
    (hsp : IsSubprotocol s p) : Nonempty (SubprotocolPath s p) := by
  induction hsp with
  | refl p => exact ⟨SubprotocolPath.refl p⟩
  | alice_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_false f P s t⟩
  | alice_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.alice_true f P s t⟩
  | bob_false f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_false f P s t⟩
  | bob_true f P s hs ih =>
    rcases ih with ⟨t⟩
    exact ⟨SubprotocolPath.bob_true f P s t⟩

/-- Classical choice of a witness (a `SubprotocolPath`) from a proof that
something is a  `Subprotocol`. -/
noncomputable def choosePath {s p : Protocol X Y α}
    (hsp : IsSubprotocol s p) : SubprotocolPath s p :=
  Classical.choice (path_exists_of_isSubprotocol hsp)

/-- A `SubprotocolPath` won't have any more leaves than its parent. -/
lemma SubprotocolPath.numLeaves_le {s p : Protocol X Y α}
    (hsp : SubprotocolPath s p) : s.numLeaves ≤ p.numLeaves := by
  induction hsp with
  | refl p =>
    exact le_rfl
  | alice_false f P s hs ih =>
    have hchild : (P false).numLeaves ≤ (Protocol.alice f P).numLeaves := by
      simp [numLeaves, shape]
    exact ih.trans hchild
  | alice_true f P s hs ih =>
    have hchild : (P true).numLeaves ≤ (Protocol.alice f P).numLeaves := by
      simp [numLeaves, shape]
    exact ih.trans hchild
  | bob_false f P s hs ih =>
    have hchild : (P false).numLeaves ≤ (Protocol.bob f P).numLeaves := by
      simp [numLeaves, shape]
    exact ih.trans hchild
  | bob_true f P s hs ih =>
    have hchild : (P true).numLeaves ≤ (Protocol.bob f P).numLeaves := by
      simp [numLeaves, shape]
    exact ih.trans hchild

/-- Alice-side predicate set for the inputs that reach a chosen subprotocol path. -/
def reachXPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set X :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false f P s hs => reachXPath hs ∩ {x | f x = false}
  | SubprotocolPath.alice_true f P s hs => reachXPath hs ∩ {x | f x = true}
  | SubprotocolPath.bob_false _ _ _ hs => reachXPath hs
  | SubprotocolPath.bob_true _ _ _ hs => reachXPath hs

/-- Bob-side predicate set for the inputs that reach a chosen subprotocol path. -/
def reachYPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set Y :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false _ _ _ hs => reachYPath hs
  | SubprotocolPath.alice_true _ _ _ hs => reachYPath hs
  | SubprotocolPath.bob_false f P s hs => reachYPath hs ∩ {y | f y = false}
  | SubprotocolPath.bob_true f P s hs => reachYPath hs ∩ {y | f y = true}

/-- A `Prop` which states that inputs `x : X` and  `y : Y` will get you to a particular
`SubprotocolPath` of `p`. -/
def reachesPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) (x : X) (y : Y) : Prop :=
  x ∈ reachXPath hsp ∧ y ∈ reachYPath hsp

/-- The set of Alice's inputs that reach *any* subprotocol path to the given subprotocol. -/
def reachX {s p : Protocol X Y α} (hsp : IsSubprotocol s p) : Set X :=
  reachXPath (choosePath hsp)

/-- The set of Bob's inputs that reach *any* subprotocol path to the given subprotocol. -/
def reachY {s p : Protocol X Y α} (hsp : IsSubprotocol s p) : Set Y :=
  reachYPath (choosePath hsp)

/-- A `Prop` which states that on input `x : X` and `y : Y` the protocol `p`
reaches the subprotocol `s`. -/
def reaches {s p : Protocol X Y α} (hsp : IsSubprotocol s p) (x : X) (y : Y) : Prop :=
  x ∈ reachX hsp ∧ y ∈ reachY hsp

/-- If on input `x,y` the protocol reaches subprotocol*path* `s` of `p`, then running `s` and
running `p` produce the same output. -/
lemma subprotocol_run_eq_of_reachesPath
    {s p : Protocol X Y α} (hsp : SubprotocolPath s p) {x : X} {y : Y}
    (hxy : reachesPath hsp x y) : p.run x y = s.run x y := by
  induction hsp with
  | refl _ => rfl
  | alice_false f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfx : f x = false := hx.2
    simpa [reachesPath, reachXPath, reachYPath, Protocol.run, hfx] using ih ⟨hx.1, hy⟩
  | alice_true f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfx : f x = true := hx.2
    simpa [reachesPath, reachXPath, reachYPath, Protocol.run, hfx] using ih ⟨hx.1, hy⟩
  | bob_false f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfy : f y = false := hy.2
    simpa [reachesPath, reachXPath, reachYPath, Protocol.run, hfy] using ih ⟨hx, hy.1⟩
  | bob_true f P s hs ih =>
    rcases hxy with ⟨hx, hy⟩
    have hfy : f y = true := hy.2
    simpa [reachesPath, reachXPath, reachYPath, Protocol.run, hfy] using ih ⟨hx, hy.1⟩

/-- If on input `x,y` the protocol reaches subprotocol `s` of `p`, then running `s` and
running `p` produce the same output. -/
lemma subprotocol_run_eq_of_reaches
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : reaches hsp x y) : p.run x y = s.run x y := by
  simpa [reaches, reachX, reachY] using
    (subprotocol_run_eq_of_reachesPath (choosePath hsp) hxy)

/-- Pick a canonical output value from a protocol (leftmost leaf). -/
def chooseOutput : Protocol X Y α → α
  | .output a => a
  | .alice _ P => chooseOutput (P false)
  | .bob _ P => chooseOutput (P false)

/-- Gives you a protocol which is just `p` with the subprotocol `s` collapsed to a single leaf,
and the value at that leaf is the leftmost leaf of `s`.

We need subprotocol*path* because we need to find `s`, and that's how we do it. -/
def erasePath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    Protocol X Y α :=
  match hsp with
  | .refl p => .output (chooseOutput p)
  | .alice_false f P s hs =>
      .alice f (fun b =>
        match b with
        | false => erasePath hs
        | true => P true)
  | .alice_true f P s hs =>
      .alice f (fun b =>
        match b with
        | false => P false
        | true => erasePath hs)
  | .bob_false f P s hs =>
      .bob f (fun b =>
        match b with
        | false => erasePath hs
        | true => P true)
  | .bob_true f P s hs =>
      .bob f (fun b =>
        match b with
        | false => P false
        | true => erasePath hs)

/-- After we erase `s` from `p`, the resulting protocol has `p.numLeaves - s.numLeaves + 1`
leaves. -/
lemma erasePath_numLeaves {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    (erasePath hsp).numLeaves = p.numLeaves - s.numLeaves + 1 := by
  induction hsp with
  | refl p =>
    simp [erasePath, numLeaves, shape]
  | alice_false f P s hs ih =>
    have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.alice_false f P s hs)).numLeaves
          = (erasePath hs).numLeaves + (P true).numLeaves := by
              simp [erasePath, numLeaves, shape]
      _ = ((P false).numLeaves - s.numLeaves + 1) + (P true).numLeaves := by
            rw [ih]
      _ = (Protocol.alice f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
              simpa [numLeaves] using hle
            simp [numLeaves, shape]
            omega
  | alice_true f P s hs ih =>
    have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.alice_true f P s hs)).numLeaves
          = (P false).numLeaves + (erasePath hs).numLeaves := by
              simp [erasePath, numLeaves, shape]
      _ = (P false).numLeaves + ((P true).numLeaves - s.numLeaves + 1) := by
            rw [ih]
      _ = (Protocol.alice f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
              simpa [numLeaves] using hle
            simp [numLeaves, shape]
            omega
  | bob_false f P s hs ih =>
    have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.bob_false f P s hs)).numLeaves
          = (erasePath hs).numLeaves + (P true).numLeaves := by
              simp [erasePath, numLeaves, shape]
      _ = ((P false).numLeaves - s.numLeaves + 1) + (P true).numLeaves := by
            rw [ih]
      _ = (Protocol.bob f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
              simpa [numLeaves] using hle
            simp [numLeaves, shape]
            omega
  | bob_true f P s hs ih =>
    have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
    calc
      (erasePath (SubprotocolPath.bob_true f P s hs)).numLeaves
          = (P false).numLeaves + (erasePath hs).numLeaves := by
              simp [erasePath, numLeaves, shape]
      _ = (P false).numLeaves + ((P true).numLeaves - s.numLeaves + 1) := by
            rw [ih]
      _ = (Protocol.bob f P).numLeaves - s.numLeaves + 1 := by
            have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
              simpa [numLeaves] using hle
            simp [numLeaves, shape]
            omega

/-- If the input doesn't reach a subprotocolpath `s`, then running `p` on that input
is the same as running `p` with `s` erased. -/
lemma erasePath_run_outside
    {s p : Protocol X Y α} (hsp : SubprotocolPath s p) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    (erasePath hsp).run x y = p.run x y := by
  induction hsp with
  | refl p =>
    exfalso
    exact hxy (by simp [reachesPath, reachXPath, reachYPath])
  | alice_false f P s hs ih =>
    by_cases hfx : f x = false
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      have := ih hxy'
      simpa [erasePath, Protocol.run, hfx] using this
    · have hfx' : f x = true := by
        cases h : f x <;> simp_all
      simp [erasePath, Protocol.run, hfx']
  | alice_true f P s hs ih =>
    by_cases hfx : f x = true
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      have := ih hxy'
      simpa [erasePath, Protocol.run, hfx] using this
    · have hfx' : f x = false := by
        cases h : f x <;> simp_all
      simp [erasePath, Protocol.run, hfx']
  | bob_false f P s hs ih =>
    by_cases hfy : f y = false
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      have := ih hxy'
      simpa [erasePath, Protocol.run, hfy] using this
    · have hfy' : f y = true := by
        cases h : f y <;> simp_all
      simp [erasePath, Protocol.run, hfy']
  | bob_true f P s hs ih =>
    by_cases hfy : f y = true
    · have hxy' : ¬ reachesPath hs x y := by
        intro hreach
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      have := ih hxy'
      simpa [erasePath, Protocol.run, hfy] using this
    · have hfy' : f y = false := by
        cases h : f y <;> simp_all
      simp [erasePath, Protocol.run, hfy']

/-- Subprotocol *not*-path versions of the above. -/
noncomputable def erase {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    Protocol X Y α :=
  erasePath (choosePath hsp)

lemma erase_numLeaves {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    (erase hsp).numLeaves = p.numLeaves - s.numLeaves + 1 := by
  simpa [erase] using erasePath_numLeaves (choosePath hsp)

lemma erase_run_outside
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (erase hsp).run x y = p.run x y := by
  simpa [erase, reaches, reachX, reachY] using
    (erasePath_run_outside (choosePath hsp) hxy)

/-- Delete a selected subtree by splicing; returns `none` only at the root case. -/
def deletePath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    Option (Protocol X Y α) :=
  match hsp with
  | .refl _ => none
  | .alice_false f P s hs =>
      match deletePath hs with
      | none => some (P true)
      | some q => some (.alice f (fun b => if b then P true else q))
  | .alice_true f P s hs =>
      match deletePath hs with
      | none => some (P false)
      | some q => some (.alice f (fun b => if b then q else P false))
  | .bob_false f P s hs =>
      match deletePath hs with
      | none => some (P true)
      | some q => some (.bob f (fun b => if b then P true else q))
  | .bob_true f P s hs =>
      match deletePath hs with
      | none => some (P false)
      | some q => some (.bob f (fun b => if b then q else P false))

lemma deletePath_ne_none_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) : deletePath hsp ≠ none := by
  induction hsp with
  | refl p =>
    exact (Nat.lt_irrefl _ hlt).elim
  | alice_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]
  | alice_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]
  | bob_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]
  | bob_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel]

lemma deletePath_exists_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    ∃ q, deletePath hsp = some q := by
  cases hdel : deletePath hsp with
  | none =>
    exfalso
    exact (deletePath_ne_none_of_lt hsp hlt) hdel
  | some q =>
    exact ⟨q, rfl⟩

noncomputable def prunePath {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) : Protocol X Y α :=
  Classical.choose (deletePath_exists_of_lt hsp hlt)

lemma prunePath_spec {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    deletePath hsp = some (prunePath hsp hlt) :=
  Classical.choose_spec (deletePath_exists_of_lt hsp hlt)

lemma eq_of_deletePath_none {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hnone : deletePath hsp = none) : s = p := by
  cases hsp with
  | refl p =>
    rfl
  | alice_false f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | alice_true f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_false f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_true f P s hs =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone

lemma deletePath_numLeaves_of_some {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    {q : Protocol X Y α} (hq : deletePath hsp = some q) :
    q.numLeaves = p.numLeaves - s.numLeaves := by
  induction hsp generalizing q with
  | refl p =>
    simp [deletePath] at hq
  | alice_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P false := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [numLeaves, shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P false).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P false).shape.numLeaves - s.shape.numLeaves := by
        simpa [numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
        simpa [numLeaves] using hle
      simp [numLeaves, shape, hchildEq']
      omega
  | alice_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P true := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [numLeaves, shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P true).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P true).shape.numLeaves - s.shape.numLeaves := by
        simpa [numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
        simpa [numLeaves] using hle
      simp [numLeaves, shape, hchildEq']
      omega
  | bob_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P false := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [numLeaves, shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P false).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P false).shape.numLeaves - s.shape.numLeaves := by
        simpa [numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P false).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P false).shape.numLeaves := by
        simpa [numLeaves] using hle
      simp [numLeaves, shape, hchildEq']
      omega
  | bob_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      simp [deletePath, hchild] at hq
      subst q
      have hsEq : s = P true := eq_of_deletePath_none hs hchild
      subst hsEq
      simp [numLeaves, shape]
    | some qchild =>
      simp [deletePath, hchild] at hq
      subst q
      have hchildEq : qchild.numLeaves = (P true).numLeaves - s.numLeaves :=
        ih hchild
      have hchildEq' : qchild.shape.numLeaves = (P true).shape.numLeaves - s.shape.numLeaves := by
        simpa [numLeaves] using hchildEq
      have hle : s.numLeaves ≤ (P true).numLeaves := SubprotocolPath.numLeaves_le hs
      have hle' : s.shape.numLeaves ≤ (P true).shape.numLeaves := by
        simpa [numLeaves] using hle
      simp [numLeaves, shape, hchildEq']
      omega

lemma prunePath_numLeaves_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    (prunePath hsp hlt).numLeaves = p.numLeaves - s.numLeaves := by
  simpa [prunePath] using deletePath_numLeaves_of_some hsp (prunePath_spec hsp hlt)

lemma reachesPath_of_deletePath_none {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hnone : deletePath hsp = none) (x : X) (y : Y) : reachesPath hsp x y := by
  induction hsp with
  | refl p =>
    simp [reachesPath, reachXPath, reachYPath]
  | alice_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | alice_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_false f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone
  | bob_true f P s hs ih =>
    cases hdel : deletePath hs <;> simp [deletePath, hdel] at hnone

lemma deletePath_run_outside_of_some {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    {q : Protocol X Y α} (hq : deletePath hsp = some q) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    q.run x y = p.run x y := by
  induction hsp generalizing q with
  | refl p =>
    simp [deletePath] at hq
  | alice_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P true := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = false
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      · have hfx' : f x = true := by cases h : f x <;> simp_all
        simp [Protocol.run, hfx']
    | some qchild =>
      have hq' : q = alice f (fun b => if b = true then P true else qchild) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = false
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
        have hrec : qchild.run x y = (P false).run x y := ih hchild hxy'
        simp [Protocol.run, hfx, hrec]
      · have hfx' : f x = true := by cases h : f x <;> simp_all
        simp [Protocol.run, hfx']
  | alice_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P false := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = true
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
      · have hfx' : f x = false := by cases h : f x <;> simp_all
        simp [Protocol.run, hfx']
    | some qchild =>
      have hq' : q = alice f (fun b => if b = true then qchild else P false) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfx : f x = true
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfx] using hreach)
        have hrec : qchild.run x y = (P true).run x y := ih hchild hxy'
        simp [Protocol.run, hfx, hrec]
      · have hfx' : f x = false := by cases h : f x <;> simp_all
        simp [Protocol.run, hfx']
  | bob_false f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P true := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = false
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      · have hfy' : f y = true := by cases h : f y <;> simp_all
        simp [Protocol.run, hfy']
    | some qchild =>
      have hq' : q = bob f (fun b => if b = true then P true else qchild) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = false
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
        have hrec : qchild.run x y = (P false).run x y := ih hchild hxy'
        simp [Protocol.run, hfy, hrec]
      · have hfy' : f y = true := by cases h : f y <;> simp_all
        simp [Protocol.run, hfy']
  | bob_true f P s hs ih =>
    cases hchild : deletePath hs with
    | none =>
      have hq' : q = P false := by simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = true
      · exfalso
        have hreach : reachesPath hs x y := reachesPath_of_deletePath_none hs hchild x y
        exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
      · have hfy' : f y = false := by cases h : f y <;> simp_all
        simp [Protocol.run, hfy']
    | some qchild =>
      have hq' : q = bob f (fun b => if b = true then qchild else P false) := by
        simpa [deletePath, hchild] using hq.symm
      subst q
      by_cases hfy : f y = true
      · have hxy' : ¬ reachesPath hs x y := by
          intro hreach
          exact hxy (by simpa [reachesPath, reachXPath, reachYPath, hfy] using hreach)
        have hrec : qchild.run x y = (P true).run x y := ih hchild hxy'
        simp [Protocol.run, hfy, hrec]
      · have hfy' : f y = false := by cases h : f y <;> simp_all
        simp [Protocol.run, hfy']

lemma prunePath_run_outside_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    (prunePath hsp hlt).run x y = p.run x y := by
  exact deletePath_run_outside_of_some hsp (prunePath_spec hsp hlt) hxy

noncomputable def prune {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) : Protocol X Y α :=
  prunePath (choosePath hsp) hlt

lemma prune_numLeaves_of_lt {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) :
    (prune hsp hlt).numLeaves = p.numLeaves - s.numLeaves := by
  simpa [prune] using prunePath_numLeaves_of_lt (choosePath hsp) hlt

lemma prune_run_outside_of_lt {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (prune hsp hlt).run x y = p.run x y := by
  simpa [prune, reaches, reachX, reachY] using
    (prunePath_run_outside_of_lt (choosePath hsp) hlt hxy)


noncomputable def testSubprotocol {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : Protocol X Y α) : Protocol X Y α :=
  Protocol.alice (fun x => by
    classical
    exact decide (x ∈ reachX hsp)) (fun bx =>
    Protocol.bob (fun y => by
      classical
      exact decide (y ∈ reachY hsp)) (fun bY =>
        if bx && bY then qIn else qOut))

@[simp] lemma testSubprotocol_complexity
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : Protocol X Y α) :
    (testSubprotocol hsp qIn qOut).complexity =
      2 + max qIn.complexity qOut.complexity := by
  simp [testSubprotocol, complexity, Nat.max_comm]
  omega

lemma testSubprotocol_run_inside
    {s p qIn qOut : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : reaches hsp x y) :
    (testSubprotocol hsp qIn qOut).run x y = qIn.run x y := by
  rcases hxy with ⟨hx, hy⟩
  simp [testSubprotocol, Protocol.run, hx, hy]

lemma testSubprotocol_run_outside
    {s p qIn qOut : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (testSubprotocol hsp qIn qOut).run x y = qOut.run x y := by
  by_cases hx : x ∈ reachX hsp
  · have hy : y ∉ reachY hsp := by
      intro hy
      exact hxy ⟨hx, hy⟩
    simp [testSubprotocol, Protocol.run, hx, hy]
  · simp [testSubprotocol, Protocol.run, hx]

end Deterministic.Protocol

end CommunicationComplexity
