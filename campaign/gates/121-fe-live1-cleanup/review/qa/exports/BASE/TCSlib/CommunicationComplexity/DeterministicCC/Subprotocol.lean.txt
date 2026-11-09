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

Subtrees of a deterministic protocol tree, the inputs whose run passes through a given
subtree, and the tree surgery used to balance a protocol in the proof of [RY20, Thm 1.3]:
collapsing a subtree to a single leaf (`erase`), splicing it out in favour of its sibling
(`prune`), and the two-bit test protocol (`testSubprotocol`) with which the two parties check
whether their input is consistent with the path to the subtree.

## Main definitions

- `Deterministic.Protocol.IsSubprotocol`: inductive predicate asserting that one protocol is a
  rooted subtree of another
- `Deterministic.Protocol.SubprotocolPath`: the type-valued version, recording the sequence of
  branch choices from the root of the ambient protocol to the root of the subtree
- `Deterministic.Protocol.reaches` / `Deterministic.Protocol.reachesPath`: the input follows
  the (chosen / given) path to the subtree
- `Deterministic.Protocol.erase` / `Deterministic.Protocol.erasePath`: collapse a subtree to a
  single leaf
- `Deterministic.Protocol.prune` / `Deterministic.Protocol.prunePath` /
  `Deterministic.Protocol.deletePath`: delete a subtree, replacing its parent by its sibling
- `Deterministic.Protocol.testSubprotocol`: a two-bit test protocol that routes inputs to one
  of two sub-protocols based on whether they reach a given subprotocol

## Main results

- `Deterministic.Protocol.balanced_subprotocol`: every protocol with more than one leaf has a
  subprotocol with a balanced (⅓–⅔) fraction of its leaves [RY20, Lemma 1.4]
- `Deterministic.Protocol.erase_numLeaves` / `Deterministic.Protocol.erase_run_outside`:
  erasing a subtree with `r` leaves from a protocol with `ℓ` leaves gives `ℓ - r + 1` leaves
  and does not change the output on inputs that do not reach the subtree
- `Deterministic.Protocol.prune_numLeaves_of_lt` /
  `Deterministic.Protocol.prune_run_outside_of_lt`: pruning gives `ℓ - r` leaves and does not
  change the output on inputs that do not reach the subtree
- `Deterministic.Protocol.testSubprotocol_run_inside` /
  `Deterministic.Protocol.testSubprotocol_run_outside` /
  `Deterministic.Protocol.testSubprotocol_complexity`: the test protocol runs the "inside"
  protocol on inputs that reach the subtree and the "outside" protocol otherwise, at a cost
  of two bits plus the larger of the two costs

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*, Cambridge University
  Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

namespace Deterministic.Protocol

variable {X Y α : Type*}

/-- `IsSubprotocol s p` means that the protocol tree `s` is a rooted subtree of the protocol
tree `p`: either `s` is `p` itself, or `s` is a subtree of one of the two children of the root
of `p`. This is the subtree rooted at a vertex `v` of the protocol tree in
[RY20, Thm 1.3 proof]. -/
inductive IsSubprotocol : Protocol X Y α → Protocol X Y α → Prop where
| refl : ∀ p, IsSubprotocol p p
| alice_false : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.alice f P)
| alice_true  : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.alice f P)
| bob_false   : ∀ f P s, IsSubprotocol s (P false) → IsSubprotocol s (Protocol.bob f P)
| bob_true    : ∀ f P s, IsSubprotocol s (P true)  → IsSubprotocol s (Protocol.bob f P)

/-- If `s` is a subprotocol of `t` and `t` is a subprotocol of `u`, then `s` is a subprotocol
of `u`: the subtree relation is transitive. Proved by induction on the path from `u` to `t`. -/
lemma IsSubprotocol.trans
    {s t u : Protocol X Y α}
    (h1 : IsSubprotocol s t) (h2 : IsSubprotocol t u) : IsSubprotocol s u := by
  induction h2 with
  | refl _ => exact h1
  | alice_false f P t ht ih => exact IsSubprotocol.alice_false f P s (ih h1)
  | alice_true f P t ht ih => exact IsSubprotocol.alice_true f P s (ih h1)
  | bob_false f P t ht ih => exact IsSubprotocol.bob_false f P s (ih h1)
  | bob_true f P t ht ih => exact IsSubprotocol.bob_true f P s (ih h1)

/-- Each child of an `alice` node is a subprotocol of the node. -/
private lemma IsSubprotocol.alice_child (f : X → Bool) (P : Bool → Protocol X Y α) (b : Bool) :
    IsSubprotocol (P b) (Protocol.alice f P) := by
  cases b
  · exact IsSubprotocol.alice_false f P _ (IsSubprotocol.refl _)
  · exact IsSubprotocol.alice_true f P _ (IsSubprotocol.refl _)

/-- Each child of a `bob` node is a subprotocol of the node. -/
private lemma IsSubprotocol.bob_child (f : Y → Bool) (P : Bool → Protocol X Y α) (b : Bool) :
    IsSubprotocol (P b) (Protocol.bob f P) := by
  cases b
  · exact IsSubprotocol.bob_false f P _ (IsSubprotocol.refl _)
  · exact IsSubprotocol.bob_true f P _ (IsSubprotocol.refl _)

/-- Child-selection step shared by `balanced_aux` and `balanced_subprotocol`. At a node `p`
with children `P false`, `P true` and at least `2n/3` leaves in total, the larger child has at
least `n/3` leaves; either it is already balanced, or it still has at least `2n/3` leaves and
the search continues inside it (`ih`). -/
private lemma balanced_children (p : Protocol X Y α) (P : Bool → Protocol X Y α) (n : ℕ)
    (hP : ∀ b, IsSubprotocol (P b) p)
    (htot : 3 * ((P false).numLeaves + (P true).numLeaves) ≥ 2 * n)
    (ih : ∀ b, 3 * (P b).numLeaves ≥ 2 * n →
      ∃ s : Protocol X Y α, IsSubprotocol s (P b) ∧ 3 * s.numLeaves ≥ n ∧
        3 * s.numLeaves < 2 * n) :
    ∃ s : Protocol X Y α, IsSubprotocol s p ∧ 3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  -- Step 1: the larger child `P b` has at least `n/3` leaves
  obtain ⟨b, hb⟩ : ∃ b : Bool, 3 * (P b).numLeaves ≥ n := by
    by_cases hcmp : (P false).numLeaves ≥ (P true).numLeaves
    · exact ⟨false, by omega⟩
    · exact ⟨true, by omega⟩
  by_cases hlt : 3 * (P b).numLeaves < 2 * n
  · -- Step 2: the larger child is already balanced
    exact ⟨P b, hP b, hb, hlt⟩
  · -- Step 3: otherwise recurse into the larger child
    obtain ⟨s, hs, hs1, hs2⟩ := ih b (by omega)
    exact ⟨s, hs.trans (hP b), hs1, hs2⟩

/-- The descent step of `balanced_subprotocol`, with the target leaf count `n` decoupled from
the protocol: if `n > 1` and `p` has at least `2n/3` leaves (`3 · numLeaves p ≥ 2n`), then `p`
has a subprotocol whose leaf count `r` satisfies `n ≤ 3r < 2n`.

**Proof sketch.** Induction on `p`, carrying the fixed threshold `n`.
(1) A single leaf is impossible: it has one leaf, and `3 ≥ 2n` contradicts `n > 1`.
(2) At an `alice` or `bob` node the leaf count is the sum over the two children, so the
child-selection lemma `balanced_children` applies: the larger child has at least `n/3` leaves;
either it has fewer than `2n/3` leaves and is the witness, or it still has at least `2n/3`
leaves and the induction hypothesis finds the witness inside it. This is the walk down the
path of heavier children in [RY20, Lemma 1.4 proof], organised as structural induction. -/
private lemma balanced_aux (p : Protocol X Y α) (n : ℕ) (hn : 1 < n)
    (h : 3 * p.numLeaves ≥ 2 * n) :
    ∃ s : Protocol X Y α,
      IsSubprotocol s p ∧ 3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction p with
  | output v =>
    -- Step 1: a single leaf has one leaf, so `3 ≥ 2n` contradicts `n > 1`
    simp [numLeaves, shape] at h
    omega
  | alice f P ih =>
    -- Step 2: select the larger child (`balanced_children`); the children embed via `alice_child`
    exact balanced_children _ P n (IsSubprotocol.alice_child f P)
      (by simpa [numLeaves, shape] using h) ih
  | bob f P ih =>
    -- Step 2 (bob node): the same selection, the children embedding via `bob_child`
    exact balanced_children _ P n (IsSubprotocol.bob_child f P)
      (by simpa [numLeaves, shape] using h) ih

/-- Every protocol tree with `ℓ > 1` leaves has a subtree whose number of leaves `r` satisfies
`ℓ/3 ≤ r < 2ℓ/3` (precisely, `3r ≥ ℓ` and `3r < 2ℓ`). [RY20, Lemma 1.4]. Deviation: the
source states `ℓ/3 ≤ r ≤ 2ℓ/3` with no hypothesis on `ℓ`; the formal statement has the strict
upper bound, which the proof gives directly, and assumes `ℓ > 1`, without which no such
subtree exists (a single leaf has `r = ℓ = 1 > 2ℓ/3`).

**Proof sketch.** The proof is a short instantiation of the child-selection lemma
`balanced_children` with the threshold `n = ℓ`; the recursion below the root is
`balanced_aux`. (1) A single leaf is excluded by `ℓ > 1`. (2) At the root node the leaf count
`ℓ` is the sum of the two children's leaf counts (`hsum`), so the root has at least `2ℓ/3`
leaves trivially. (3) `balanced_children` applies: the larger child has at least `ℓ/3` leaves;
if it has fewer than `2ℓ/3` it is the witness, otherwise `balanced_aux` (with the threshold
`ℓ` still fixed) descends into it. This is the walk down the path of heavier children in
[RY20, Lemma 1.4 proof], with the stopping condition checked at each vertex. -/
theorem balanced_subprotocol (p : Protocol X Y α) (hn : 1 < p.numLeaves) :
    ∃ s : Protocol X Y α,
      IsSubprotocol s p ∧ 3 * s.numLeaves ≥ p.numLeaves ∧
      3 * s.numLeaves < 2 * p.numLeaves := by
  induction p with
  | output v =>
    -- Step 1: a single leaf has one leaf, contradicting `ℓ > 1`
    simp [numLeaves, shape] at hn
  | alice f P _ =>
    -- Step 2: the node's leaf count is the sum of its children's
    have hsum : (Protocol.alice f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [numLeaves, shape]
    rw [hsum] at hn ⊢
    -- Step 3: select the larger child; inside it, `balanced_aux` finds a balanced subprotocol
    exact balanced_children _ P _ (IsSubprotocol.alice_child f P) (by omega)
      (fun b hb => balanced_aux (P b) _ hn hb)
  | bob f P _ =>
    -- Steps 2–3 (bob node): identical, with the children embedding via `bob_child`
    have hsum : (Protocol.bob f P).numLeaves =
        (P false).numLeaves + (P true).numLeaves := by
      simp [numLeaves, shape]
    rw [hsum] at hn ⊢
    exact balanced_children _ P _ (IsSubprotocol.bob_child f P) (by omega)
      (fun b hb => balanced_aux (P b) _ hn hb)

/-- `SubprotocolPath s p` is the type of paths from the root of `p` to the root of a subtree
`s`: the sequence of branch choices (`false`/`true` at each `alice` or `bob` node passed) that
leads from `p` to `s`. It is the data-carrying version of `IsSubprotocol s p`, used to define
the tree surgery (`erasePath`, `deletePath`) by recursion on the path. -/
inductive SubprotocolPath : Protocol X Y α → Protocol X Y α → Type _ where
| refl : ∀ p, SubprotocolPath p p
| alice_false : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.alice f P)
| alice_true  : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.alice f P)
| bob_false   : ∀ f P s, SubprotocolPath s (P false) → SubprotocolPath s (Protocol.bob f P)
| bob_true    : ∀ f P s, SubprotocolPath s (P true)  → SubprotocolPath s (Protocol.bob f P)

/-- Forgetting the data of a path from `p` to `s` gives a proof that `s` is a subprotocol of
`p`. -/
def SubprotocolPath.toIsSubprotocol {s p : Protocol X Y α} :
    SubprotocolPath s p → IsSubprotocol s p
  | .refl p => IsSubprotocol.refl p
  | .alice_false f P s hs => IsSubprotocol.alice_false f P s (hs.toIsSubprotocol)
  | .alice_true f P s hs => IsSubprotocol.alice_true f P s (hs.toIsSubprotocol)
  | .bob_false f P s hs => IsSubprotocol.bob_false f P s (hs.toIsSubprotocol)
  | .bob_true f P s hs => IsSubprotocol.bob_true f P s (hs.toIsSubprotocol)

/-- If `s` is a subprotocol of `p`, then there exists a path from the root of `p` to the root
of `s`; that is, the type `SubprotocolPath s p` is nonempty. Proved by induction on the
subprotocol derivation, which is itself a path. -/
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

/-- A classically chosen path (a `SubprotocolPath s p`) from a proof that `s` is a subprotocol
of `p` (an `IsSubprotocol s p`). When `s` occurs at several positions in `p`, this fixes one of
them; `reachX`, `reachY`, `erase` and `prune` all refer to this choice. -/
noncomputable def choosePath {s p : Protocol X Y α}
    (hsp : IsSubprotocol s p) : SubprotocolPath s p :=
  Classical.choice (path_exists_of_isSubprotocol hsp)

/-- If there is a path from the root of `p` to the root of `s`, then `s` has at most as many
leaves as `p`.

**Proof sketch.** Induction on the path. The empty path is trivial. In each of the four node
cases (Alice or Bob node, branch `false` or `true`) the child the path enters has at most as
many leaves as the node, because a node's leaf count is the sum of its two children's; chain
this with the induction hypothesis for the remaining path. -/
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

/-- The set of Alice's inputs `x` that are consistent with every Alice-move on the given path
from the root of `p` to the root of `s`: at each `alice f` node on the path, `f x` is the bit
the path takes. Bob's nodes impose no condition on `x`. -/
def reachXPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set X :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false f P s hs => reachXPath hs ∩ {x | f x = false}
  | SubprotocolPath.alice_true f P s hs => reachXPath hs ∩ {x | f x = true}
  | SubprotocolPath.bob_false _ _ _ hs => reachXPath hs
  | SubprotocolPath.bob_true _ _ _ hs => reachXPath hs

/-- The set of Bob's inputs `y` that are consistent with every Bob-move on the given path
from the root of `p` to the root of `s`: at each `bob f` node on the path, `f y` is the bit the
path takes. Alice's nodes impose no condition on `y`. -/
def reachYPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) : Set Y :=
  match hsp with
  | SubprotocolPath.refl _ => Set.univ
  | SubprotocolPath.alice_false _ _ _ hs => reachYPath hs
  | SubprotocolPath.alice_true _ _ _ hs => reachYPath hs
  | SubprotocolPath.bob_false f P s hs => reachYPath hs ∩ {y | f y = false}
  | SubprotocolPath.bob_true f P s hs => reachYPath hs ∩ {y | f y = true}

/-- The input `(x, y)` follows the given path from the root of `p` to the root of `s`: `x` is
consistent with all Alice-moves on the path and `y` with all Bob-moves, so the run of `p` on
`(x, y)` passes through the root of `s`. -/
def reachesPath {s p : Protocol X Y α} (hsp : SubprotocolPath s p) (x : X) (y : Y) : Prop :=
  x ∈ reachXPath hsp ∧ y ∈ reachYPath hsp

/-- The set of Alice's inputs consistent with the classically chosen path (`choosePath hsp`)
from the root of `p` to the root of the subprotocol `s`. Only this one path is used: if `s`
occurs at several positions in `p`, an input that reaches `s` only along a different path
need not lie in this set. -/
def reachX {s p : Protocol X Y α} (hsp : IsSubprotocol s p) : Set X :=
  reachXPath (choosePath hsp)

/-- The set of Bob's inputs consistent with the classically chosen path (`choosePath hsp`)
from the root of `p` to the root of the subprotocol `s`. As for `reachX`, only this one path is
used. -/
def reachY {s p : Protocol X Y α} (hsp : IsSubprotocol s p) : Set Y :=
  reachYPath (choosePath hsp)

/-- The input `(x, y)` reaches the subprotocol `s` of `p` along the chosen path: `x` lies in
`reachX hsp` and `y` in `reachY hsp`. Since the conditions on `x` and on `y` are separate, the
set of such inputs is a combinatorial rectangle. -/
def reaches {s p : Protocol X Y α} (hsp : IsSubprotocol s p) (x : X) (y : Y) : Prop :=
  x ∈ reachX hsp ∧ y ∈ reachY hsp

/-- If the input `(x, y)` follows the given path from `p` to its subtree `s`, then running `p`
on `(x, y)` gives the same output as running `s` on `(x, y)`.

**Proof sketch.** Induction on the path. The empty path is reflexivity. At an Alice node the
reachability hypothesis splits into membership in the shorter path's input sets and the
condition that Alice's bit on `x` is the bit the path takes; so running the node on `(x, y)`
unfolds to running the child the path enters, and the induction hypothesis applied to the
shorter path finishes. Bob nodes are symmetric, with the condition on `y`. -/
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

/-- If the input `(x, y)` reaches the subprotocol `s` of `p` (along the chosen path), then
running `p` on `(x, y)` gives the same output as running `s` on `(x, y)`. -/
lemma subprotocol_run_eq_of_reaches
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : reaches hsp x y) : p.run x y = s.run x y := by
  simpa [reaches, reachX, reachY] using
    (subprotocol_run_eq_of_reachesPath (choosePath hsp) hxy)

/-- The output label at the leftmost leaf of a protocol, reached by taking the `false` branch
at every node. It is the label given to the leaf that replaces an erased subtree. -/
def chooseOutput : Protocol X Y α → α
  | .output a => a
  | .alice _ P => chooseOutput (P false)
  | .bob _ P => chooseOutput (P false)

/-- The protocol obtained from `p` by collapsing the subtree `s`, located by the path `hsp`, to
a single leaf labelled with the leftmost output of `s` (`chooseOutput s`).

The construction is by recursion on the path: at its end (`refl`) the whole of `s` is replaced
by the leaf `output (chooseOutput s)`; at each `alice` or `bob` node the branch the path
continues into is replaced by its erasure and the other branch is kept unchanged. A path
(rather than a mere `IsSubprotocol` proof) is needed so that the recursion knows where `s`
sits inside `p`. -/
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

/-- Truncated-subtraction step for `erasePath_numLeaves`. Erasing `s` inside the branch `b` of a
two-child node replaces `(P b).numLeaves` by `(P b).numLeaves - s.numLeaves + 1` (this is `he`,
the induction hypothesis), so the node as a whole loses exactly `s.numLeaves - 1` leaves. -/
private lemma erasePath_numLeaves_step {s : Protocol X Y α} (P : Bool → Protocol X Y α)
    (b : Bool) (hs : SubprotocolPath s (P b)) {e : ℕ}
    (he : e = (P b).numLeaves - s.numLeaves + 1) :
    (bif b then (P false).numLeaves + e else e + (P true).numLeaves)
      = (P false).numLeaves + (P true).numLeaves - s.numLeaves + 1 := by
  have hle : s.numLeaves ≤ (P b).numLeaves := SubprotocolPath.numLeaves_le hs
  cases b <;> simp only [cond_false, cond_true] <;> omega

/-- Erasing the subtree `s` (with `r` leaves) from `p` (with `ℓ` leaves) along a path yields a
protocol with exactly `ℓ - r + 1` leaves: the `r` leaves of `s` are replaced by one.

**Proof sketch.** Induction on the path; the node cases are short instantiations of the
truncated-subtraction lemma `erasePath_numLeaves_step`. (1) At the end of the path `s = p` is
replaced by a single leaf, so the count is `ℓ - ℓ + 1 = 1`. (2) At a node whose branch `b` the
path continues into, the leaf count is the sum over the two children; the induction hypothesis
gives the count of the erased branch `b` as `(leaves of P b) - r + 1`, the other branch is
unchanged, and since `r ≤ leaves of P b` (`SubprotocolPath.numLeaves_le`) the natural-number
subtraction can be moved outside the sum. -/
lemma erasePath_numLeaves {s p : Protocol X Y α} (hsp : SubprotocolPath s p) :
    (erasePath hsp).numLeaves = p.numLeaves - s.numLeaves + 1 := by
  induction hsp with
  | refl p =>
    -- Step 1: the whole of `s = p` becomes a single leaf
    simp [erasePath, numLeaves, shape]
  -- Step 2, each node case: unfold one level of `erasePath`/`numLeaves`, then the
  -- truncated-subtraction step on the branch the path continues into.
  | alice_false f P s hs ih =>
    simpa [erasePath, numLeaves, shape] using erasePath_numLeaves_step P false hs ih
  | alice_true f P s hs ih =>
    simpa [erasePath, numLeaves, shape] using erasePath_numLeaves_step P true hs ih
  | bob_false f P s hs ih =>
    simpa [erasePath, numLeaves, shape] using erasePath_numLeaves_step P false hs ih
  | bob_true f P s hs ih =>
    simpa [erasePath, numLeaves, shape] using erasePath_numLeaves_step P true hs ih

/-- One-branch step for `erasePath_run_outside`. At a node `N P` (`N` is `alice f` or `bob f`)
whose input bit is `c`, with the path continuing into the branch `b`, replacing that branch by
its erasure (`Q b = erasePath hs`, `Q (!b) = P (!b)`) does not change the run on inputs that do
not follow the path. -/
private lemma erasePath_run_outside_branch {s r : Protocol X Y α} (hs : SubprotocolPath s r)
    {x : X} {y : Y} (P : Bool → Protocol X Y α) (b : Bool) (hPb : P b = r)
    (N : (Bool → Protocol X Y α) → Protocol X Y α) (c : Bool) (Q : Bool → Protocol X Y α)
    (hN : ∀ Q, (N Q).run x y = (Q c).run x y)
    (hQb : Q b = erasePath hs) (hQnb : Q (!b) = P (!b))
    (hnot : reachesPath hs x y → c ≠ b)
    (ih : ¬ reachesPath hs x y → (erasePath hs).run x y = r.run x y) :
    (N Q).run x y = (N P).run x y := by
  subst hPb
  rw [hN, hN]
  by_cases hcb : c = b
  · -- Step 1: the input enters the erased branch `b`, so it does not reach `s`: induction
    -- hypothesis
    subst hcb
    rw [hQb]
    exact ih (fun hr => hnot hr rfl)
  · -- Step 2: the input takes the untouched branch `!b`
    obtain rfl : c = !b := by cases b <;> cases c <;> first | rfl | exact absurd rfl hcb
    rw [hQnb]

/-- If the input `(x, y)` does not follow the path from `p` to its subtree `s`, then running
`p` with `s` erased on `(x, y)` gives the same output as running `p` itself: erasure only
changes the behaviour on inputs that reach `s`.

**Proof sketch.** Induction on the path; the node cases are short instantiations of the
one-branch lemma `erasePath_run_outside_branch`. (1) At the end of the path every input
follows the (empty) path, contradicting the hypothesis. (2) At a node whose branch `b` the path
continues into, the input's bit at the node is `f x` (Alice) or `f y` (Bob). If that bit is
`b`, the input enters the erased branch; since it does not follow the whole path it does not
reach `s` below, and the induction hypothesis applies. If the bit is not `b`, the input takes
the other branch, which erasure left unchanged. -/
lemma erasePath_run_outside
    {s p : Protocol X Y α} (hsp : SubprotocolPath s p) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    (erasePath hsp).run x y = p.run x y := by
  induction hsp with
  | refl p =>
    -- Step 1: every input follows the empty path, contradicting `hxy`
    exfalso
    exact hxy (by simp [reachesPath, reachXPath, reachYPath])
  -- Step 2, each node case: the input's bit at the node is `f x` (alice) or `f y` (bob); if it
  -- follows the path, `hxy` says the input does not reach `s` below, and the branch lemma
  -- finishes.
  | alice_false f P s hs ih =>
    exact erasePath_run_outside_branch hs P false rfl (alice f) (f x) _ (fun _ => rfl) rfl rfl
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih
  | alice_true f P s hs ih =>
    exact erasePath_run_outside_branch hs P true rfl (alice f) (f x) _ (fun _ => rfl) rfl rfl
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih
  | bob_false f P s hs ih =>
    exact erasePath_run_outside_branch hs P false rfl (bob f) (f y) _ (fun _ => rfl) rfl rfl
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih
  | bob_true f P s hs ih =>
    exact erasePath_run_outside_branch hs P true rfl (bob f) (f y) _ (fun _ => rfl) rfl rfl
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih

/-- The protocol obtained from `p` by collapsing its subprotocol `s` to a single leaf
(labelled with the leftmost output of `s`), along the classically chosen path to `s`. This is
a variant of the deletion step in [RY20, Thm 1.3 proof] in which the subtree at the vertex `v`
is replaced by a leaf rather than by its sibling (for the latter see `prune`). -/
noncomputable def erase {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    Protocol X Y α :=
  erasePath (choosePath hsp)

/-- Erasing the subprotocol `s` (with `r` leaves) from `p` (with `ℓ` leaves) yields a protocol
with exactly `ℓ - r + 1` leaves. -/
lemma erase_numLeaves {s p : Protocol X Y α} (hsp : IsSubprotocol s p) :
    (erase hsp).numLeaves = p.numLeaves - s.numLeaves + 1 := by
  simpa [erase] using erasePath_numLeaves (choosePath hsp)

/-- If the input `(x, y)` does not reach the subprotocol `s` of `p` (along the chosen path),
then running `p` with `s` erased on `(x, y)` gives the same output as running `p`. -/
lemma erase_run_outside
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (erase hsp).run x y = p.run x y := by
  simpa [erase, reaches, reachX, reachY] using
    (erasePath_run_outside (choosePath hsp) hxy)

/-- The protocol obtained from `p` by deleting the subtree `s`, located by the path `hsp`, and
splicing its sibling into the place of their common parent; this is the "delete `v`, replacing
`v`'s parent by `v`'s sibling" step of [RY20, Thm 1.3 proof]. The result is `none` exactly
when the path is empty (`s = p`), since deleting the whole tree leaves nothing.

The construction is by recursion on the path: at a node whose branch `b` the path continues
into, if deleting `s` from the branch `b` leaves nothing (the path ends at that child), the
node is replaced by the other child `P (!b)`; otherwise the branch `b` is replaced by the
result of the recursive deletion and the other branch is kept unchanged. -/
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

/-- If the subtree `s` has strictly fewer leaves than `p`, then deleting `s` from `p` along
a path does not delete everything: `deletePath` returns `some` protocol. (The path cannot be
empty, since then `s = p`.) -/
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

/-- If the subtree `s` has strictly fewer leaves than `p`, then there is a protocol `q` with
`deletePath hsp = some q`; the existential form of `deletePath_ne_none_of_lt`. -/
lemma deletePath_exists_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    ∃ q, deletePath hsp = some q := by
  cases hdel : deletePath hsp with
  | none =>
    exfalso
    exact (deletePath_ne_none_of_lt hsp hlt) hdel
  | some q =>
    exact ⟨q, rfl⟩

/-- The protocol obtained from `p` by deleting the subtree `s` along the path `hsp`, extracted
from the `some` value of `deletePath`, which exists because `s` has strictly fewer leaves than
`p`. -/
noncomputable def prunePath {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) : Protocol X Y α :=
  Classical.choose (deletePath_exists_of_lt hsp hlt)

/-- `prunePath hsp hlt` is the protocol returned by `deletePath hsp`, that is,
`deletePath hsp = some (prunePath hsp hlt)`. -/
lemma prunePath_spec {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    deletePath hsp = some (prunePath hsp hlt) :=
  Classical.choose_spec (deletePath_exists_of_lt hsp hlt)

/-- If deleting the subtree `s` from `p` along a path leaves nothing (`deletePath` returns
`none`), then `s` is the whole of `p`: the path is empty. -/
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

/-- One-branch step for `deletePath_numLeaves_of_some`. At a node `N P` (`N` is `alice f` or
`bob f`) with the path continuing into the branch `b`, the result of `deletePath` has exactly
`s.numLeaves` fewer leaves than the node.

**Proof sketch.** Substitute `r = P b` and expand the node's leaf count as the sum of its two
children's; then case on the result of deleting along the path inside branch `b`. (1) If the
deletion returns nothing, `s` is the whole child `P b` and `q` is the sibling `P (!b)`, so `q`
has the node's leaves minus those of `P b`. (2) If it returns `qc`, then `q` is the node
rebuilt with `qc` in branch `b` and the sibling untouched; the induction hypothesis gives the
leaf count of `qc` as that of `P b` minus that of `s`, and since `s` has at most as many
leaves as `P b` (`SubprotocolPath.numLeaves_le`) the subtraction commutes with the sum. -/
private lemma deletePath_numLeaves_branch {s r : Protocol X Y α} (hs : SubprotocolPath s r)
    (P : Bool → Protocol X Y α) (b : Bool) (hPb : P b = r)
    (N : (Bool → Protocol X Y α) → Protocol X Y α)
    {Q : Protocol X Y α → Bool → Protocol X Y α} {q : Protocol X Y α}
    (hq : (match deletePath hs with
      | none => some (P (!b))
      | some qc => some (N (Q qc))) = some q)
    (hN : ∀ Q, (N Q).numLeaves = (Q false).numLeaves + (Q true).numLeaves)
    (hQb : ∀ qc, Q qc b = qc) (hQnb : ∀ qc, Q qc (!b) = P (!b))
    (ih : ∀ {q : Protocol X Y α}, deletePath hs = some q →
      q.numLeaves = r.numLeaves - s.numLeaves) :
    q.numLeaves = (N P).numLeaves - s.numLeaves := by
  subst hPb
  rw [hN]
  cases hchild : deletePath hs with
  | none =>
    -- Step 1: `deletePath hs = none` ⇒ `s = P b`, and `q` is the sibling `P (!b)`
    have hq' : q = P (!b) := by simpa [hchild] using hq.symm
    have hsEq : s = P b := eq_of_deletePath_none hs hchild
    rw [hq', hsEq]
    cases b <;> simp only [Bool.not_false, Bool.not_true] <;> omega
  | some qc =>
    -- Step 2: `some qc` ⇒ induction hypothesis on branch `b`; the sibling `!b` is untouched
    have hq' : q = N (Q qc) := by simpa [hchild] using hq.symm
    have hqc : qc.numLeaves = (P b).numLeaves - s.numLeaves := ih hchild
    have hle : s.numLeaves ≤ (P b).numLeaves := SubprotocolPath.numLeaves_le hs
    rw [hq', hN]
    cases b <;> simp only [Bool.not_false, Bool.not_true] at hQnb hqc hle ⊢ <;>
      rw [hQb, hQnb] <;> omega

/-- If deleting the subtree `s` (with `r` leaves) from `p` (with `ℓ` leaves) along a path
yields the protocol `q`, then `q` has exactly `ℓ - r` leaves: the leaves of `s` are removed and
no others.

**Proof sketch.** Induction on the path, generalising over `q`; the node cases are short
instantiations of the one-branch lemma `deletePath_numLeaves_branch`. (1) The empty path
returns `none`, so the hypothesis is contradictory. (2) At a node whose branch `b` the path
continues into, the leaf count of the node is the sum over its two children. If the recursive
deletion in branch `b` returned `none`, then `s` is that whole child
(`eq_of_deletePath_none`) and `q` is the sibling, whose leaf count is the sum minus `r`. If it
returned `some`, the induction hypothesis gives `(leaves of P b) - r` leaves in branch `b`,
the sibling is unchanged, and `r ≤ leaves of P b` (`SubprotocolPath.numLeaves_le`) lets the
subtraction move outside the sum. -/
lemma deletePath_numLeaves_of_some {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    {q : Protocol X Y α} (hq : deletePath hsp = some q) :
    q.numLeaves = p.numLeaves - s.numLeaves := by
  induction hsp generalizing q with
  | refl p =>
    -- Step 1: the empty path returns `none`, contradicting `hq`
    simp [deletePath] at hq
  -- Step 2, each node case: the one-branch lemma with the branch the path continues into.
  | alice_false f P s hs ih =>
    exact deletePath_numLeaves_branch hs P false rfl (alice f) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ih
  | alice_true f P s hs ih =>
    exact deletePath_numLeaves_branch hs P true rfl (alice f) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ih
  | bob_false f P s hs ih =>
    exact deletePath_numLeaves_branch hs P false rfl (bob f) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ih
  | bob_true f P s hs ih =>
    exact deletePath_numLeaves_branch hs P true rfl (bob f) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) ih

/-- Pruning the subtree `s` (with `r` leaves) from `p` (with `ℓ` leaves) along a path yields
a protocol with exactly `ℓ - r` leaves. -/
lemma prunePath_numLeaves_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) :
    (prunePath hsp hlt).numLeaves = p.numLeaves - s.numLeaves := by
  simpa [prunePath] using deletePath_numLeaves_of_some hsp (prunePath_spec hsp hlt)

/-- If deleting the subtree `s` from `p` along a path leaves nothing, then every input follows
that path (the path is empty, and every input reaches the root). -/
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

/-- One-branch step for `deletePath_run_outside_of_some`. At a node `N P` (`N` is `alice f` or
`bob f`) whose input bit is `c`, with the path continuing into the branch `b`, the result of
`deletePath` runs like the node on inputs that do not follow the path.

**Proof sketch.** Substitute `r = P b`; running the node on `(x, y)` means running the child in
the input's branch `c`. Case on the result of deleting along the path inside branch `b`.
(1) If the deletion returns nothing, every input follows the path into `P b`, so the
"off the path" hypothesis forces `c ≠ b`, i.e. `c = !b`, and `q = P (!b)` is exactly the
child the input runs. (2) If it returns `qc` and `c = b`, branch `b` of `q` is `qc`; the input
does not reach `s` (otherwise it would follow the path), so the induction hypothesis gives
that `qc` runs like `P b`. (3) If it returns `qc` and `c ≠ b`, the input takes the sibling
branch, which the deletion leaves untouched. -/
private lemma deletePath_run_outside_branch {s r : Protocol X Y α} (hs : SubprotocolPath s r)
    {x : X} {y : Y} (P : Bool → Protocol X Y α) (b : Bool) (hPb : P b = r)
    (N : (Bool → Protocol X Y α) → Protocol X Y α) (c : Bool)
    {Q : Protocol X Y α → Bool → Protocol X Y α} {q : Protocol X Y α}
    (hq : (match deletePath hs with
      | none => some (P (!b))
      | some qc => some (N (Q qc))) = some q)
    (hN : ∀ Q, (N Q).run x y = (Q c).run x y)
    (hQb : ∀ qc, Q qc b = qc) (hQnb : ∀ qc, Q qc (!b) = P (!b))
    (hnot : reachesPath hs x y → c ≠ b)
    (ih : ∀ {q : Protocol X Y α}, deletePath hs = some q → ¬ reachesPath hs x y →
      q.run x y = r.run x y) :
    q.run x y = (N P).run x y := by
  subst hPb
  rw [hN]
  cases hchild : deletePath hs with
  | none =>
    -- Step 1: `deletePath hs = none` ⇒ every input follows the path at `P b`, so `c ≠ b`
    have hq' : q = P (!b) := by simpa [hchild] using hq.symm
    have hcb : c ≠ b := hnot (reachesPath_of_deletePath_none hs hchild x y)
    obtain rfl : c = !b := by cases b <;> cases c <;> first | rfl | exact absurd rfl hcb
    rw [hq']
  | some qc =>
    have hq' : q = N (Q qc) := by simpa [hchild] using hq.symm
    rw [hq', hN]
    by_cases hcb : c = b
    · -- Step 2: `some qc` and the input enters branch `b` ⇒ induction hypothesis
      subst hcb
      rw [hQb]
      exact ih hchild (fun hr => hnot hr rfl)
    · -- Step 3: the input takes the untouched branch `!b`
      obtain rfl : c = !b := by cases b <;> cases c <;> first | rfl | exact absurd rfl hcb
      rw [hQnb]

/-- If deleting the subtree `s` from `p` along a path yields the protocol `q`, then on every
input `(x, y)` that does not follow the path, `q` and `p` produce the same output: deletion
only changes the behaviour on inputs that reach `s`.

**Proof sketch.** Induction on the path, generalising over `q`; the node cases are short
instantiations of the one-branch lemma `deletePath_run_outside_branch`. (1) The empty path
returns `none`, so the hypothesis is contradictory. (2) At a node whose branch `b` the path
continues into, the input's bit at the node is `f x` (Alice) or `f y` (Bob). If the recursive
deletion in branch `b` returned `none`, every input follows the path into `b`
(`reachesPath_of_deletePath_none`), so since `(x, y)` does not follow the path its bit is not
`b`, and it takes the sibling, which is what `q` is. If it returned `some`, then either the
bit is `b`, the input enters the pruned branch without reaching `s` below, and the induction
hypothesis applies; or the bit is not `b` and the input takes the unchanged sibling. -/
lemma deletePath_run_outside_of_some {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    {q : Protocol X Y α} (hq : deletePath hsp = some q) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    q.run x y = p.run x y := by
  induction hsp generalizing q with
  | refl p =>
    -- Step 1: the empty path returns `none`, contradicting `hq`
    simp [deletePath] at hq
  -- Step 2, each node case: the one-branch lemma with the branch the path continues into; if
  -- the input follows the path at this node, `hxy` says it does not reach `s` below.
  | alice_false f P s hs ih =>
    exact deletePath_run_outside_branch hs P false rfl (alice f) (f x) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih
  | alice_true f P s hs ih =>
    exact deletePath_run_outside_branch hs P true rfl (alice f) (f x) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih
  | bob_false f P s hs ih =>
    exact deletePath_run_outside_branch hs P false rfl (bob f) (f y) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih
  | bob_true f P s hs ih =>
    exact deletePath_run_outside_branch hs P true rfl (bob f) (f y) hq (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl)
      (fun hr hc => hxy (by simpa [reachesPath, reachXPath, reachYPath, hc] using hr)) ih

/-- If the input `(x, y)` does not follow the path from `p` to its subtree `s`, then running
`p` with `s` pruned on `(x, y)` gives the same output as running `p` itself. -/
lemma prunePath_run_outside_of_lt {s p : Protocol X Y α} (hsp : SubprotocolPath s p)
    (hlt : s.numLeaves < p.numLeaves) {x : X} {y : Y}
    (hxy : ¬ reachesPath hsp x y) :
    (prunePath hsp hlt).run x y = p.run x y := by
  exact deletePath_run_outside_of_some hsp (prunePath_spec hsp hlt) hxy

/-- The protocol obtained from `p` by deleting its proper subprotocol `s` (one with strictly
fewer leaves than `p`) along the classically chosen path to `s`, and splicing the sibling of
`s` into the place of their parent. This is the "delete `v`, replacing `v`'s parent by `v`'s
sibling" step of [RY20, Thm 1.3 proof]; the balanced simulation
(`exists_balanced_simulation`) recurses on it for inputs that do not reach `s`. -/
noncomputable def prune {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) : Protocol X Y α :=
  prunePath (choosePath hsp) hlt

/-- Pruning the proper subprotocol `s` (with `r` leaves) from `p` (with `ℓ` leaves) yields a
protocol with exactly `ℓ - r` leaves. -/
lemma prune_numLeaves_of_lt {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) :
    (prune hsp hlt).numLeaves = p.numLeaves - s.numLeaves := by
  simpa [prune] using prunePath_numLeaves_of_lt (choosePath hsp) hlt

/-- If the input `(x, y)` does not reach the subprotocol `s` of `p` (along the chosen path),
then running `p` with `s` pruned on `(x, y)` gives the same output as running `p`. -/
lemma prune_run_outside_of_lt {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (hlt : s.numLeaves < p.numLeaves) {x : X} {y : Y}
    (hxy : ¬ reaches hsp x y) :
    (prune hsp hlt).run x y = p.run x y := by
  simpa [prune, reaches, reachX, reachY] using
    (prunePath_run_outside_of_lt (choosePath hsp) hlt hxy)

/-- The two-bit test protocol for a subprotocol `s` of `p`: Alice announces whether her input
is consistent with the chosen path to `s` (`x ∈ reachX hsp`), then Bob announces whether his
is (`y ∈ reachY hsp`); if both said yes the parties continue with `qIn`, otherwise with
`qOut`. This is the "each party checks whether its input is consistent with the whole path up
to `v`" step of [RY20, Thm 1.3 proof]; in the balanced simulation `qIn` simulates `s` and
`qOut` simulates `prune hsp _`. -/
noncomputable def testSubprotocol {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : Protocol X Y α) : Protocol X Y α :=
  Protocol.alice (fun x => by
    classical
    exact decide (x ∈ reachX hsp)) (fun bx =>
    Protocol.bob (fun y => by
      classical
      exact decide (y ∈ reachY hsp)) (fun bY =>
        if bx && bY then qIn else qOut))

/-- The communication cost of the test protocol is two bits (one per party) plus the larger of
the costs of the two continuations `qIn` and `qOut`. -/
@[simp] lemma testSubprotocol_complexity
    {s p : Protocol X Y α} (hsp : IsSubprotocol s p)
    (qIn qOut : Protocol X Y α) :
    (testSubprotocol hsp qIn qOut).complexity =
      2 + max qIn.complexity qOut.complexity := by
  simp [testSubprotocol, complexity, Nat.max_comm]
  omega

/-- On an input `(x, y)` that reaches the subprotocol `s` of `p` (along the chosen path), the
test protocol produces the output of the "inside" continuation `qIn`. -/
lemma testSubprotocol_run_inside
    {s p qIn qOut : Protocol X Y α} (hsp : IsSubprotocol s p) {x : X} {y : Y}
    (hxy : reaches hsp x y) :
    (testSubprotocol hsp qIn qOut).run x y = qIn.run x y := by
  rcases hxy with ⟨hx, hy⟩
  simp [testSubprotocol, Protocol.run, hx, hy]

/-- On an input `(x, y)` that does not reach the subprotocol `s` of `p` (along the chosen
path), the test protocol produces the output of the "outside" continuation `qOut`: at least one
of the two announced bits is `false`. -/
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
