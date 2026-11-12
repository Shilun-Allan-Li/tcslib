/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import Mathlib.Data.Tree.Basic
import TCSlib.CommunicationComplexity.DeterministicCC.DetBasic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Protocol Tree Shape and Leaf Count

The shape of a deterministic protocol as a bare binary tree (`Tree Unit`), the number of
leaves of a protocol, and the purely combinatorial balancing lemma on binary trees: a tree
with `ℓ > 1` leaves has a subtree with between `ℓ/3` and `2ℓ/3` leaves [RY20, Lemma 1.4].
`Subprotocol.lean` transfers this lemma to protocols and `BalancedSimulation.lean` uses it
for the `O(log ℓ)` simulation.

## Main definitions

- `Deterministic.Protocol.shape`: the underlying binary tree of a protocol, forgetting the
  message functions and outputs
- `Deterministic.Protocol.numLeaves`: the number of output leaves of a protocol tree

## Main results

- `tree_balanced_subtree`: every binary tree with more than one leaf has a subtree with
  between one third and two thirds of the total leaves

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [KN97] E. Kushilevitz, N. Nisan, *Communication Complexity*,
  Cambridge University Press, 1997.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

variable {X Y α : Type*}

namespace Deterministic.Protocol

/-- The shape of a protocol: the underlying unlabelled binary tree, with a leaf (`Tree.nil`)
for every output node and an internal node for every Alice or Bob node, whose two children
are the shapes of the continuations after sending `false` and `true`. -/
def shape : Protocol X Y α → Tree Unit
| .output _  => .nil
| .alice _ P => .node () (shape (P false)) (shape (P true))
| .bob   _ P => .node () (shape (P false)) (shape (P true))

/-- The number of leaves (output nodes) in a protocol, defined via its tree shape.
[RY20, Lemma 1.2] (the leaves of the protocol tree). -/
def numLeaves (p : Protocol X Y α) : ℕ := p.shape.numLeaves

end Deterministic.Protocol

-- TreeIsSubtree: s is a subtree of t
-- Constructor args match Tree.node : α → Tree α → Tree α → Tree α
-- so .node v l r has v:α first, then children
/-- `TreeIsSubtree s t` holds when `s` is the subtree of `t` rooted at some vertex: either
`s = t`, or `s` is a subtree of the left or of the right child of the root of `t`.
This relation is private but occurs in the statement of the public `tree_balanced_subtree`;
see that theorem's docstring. -/
private inductive TreeIsSubtree : Tree α → Tree α → Prop where
| refl  : ∀ (t : Tree α), TreeIsSubtree t t
| left  : ∀ (v : α) (s l r : Tree α), TreeIsSubtree s l → TreeIsSubtree s (.node v l r)
| right : ∀ (v : α) (s l r : Tree α), TreeIsSubtree s r → TreeIsSubtree s (.node v l r)

/-- Being a subtree is transitive: a subtree of a subtree of `u` is a subtree of `u`. -/
private lemma TreeIsSubtree.trans {s t u : Tree α} (h1 : TreeIsSubtree s t) (h2 : TreeIsSubtree t u) :
    TreeIsSubtree s u := by
  induction h2 with
  | refl _ => exact h1
  | left v s' l r hl ihl => exact TreeIsSubtree.left v s l r (ihl h1)
  | right v s' l r hr ihr => exact TreeIsSubtree.right v s l r (ihr h1)

/-- Descent lemma behind `tree_balanced_subtree`, with the threshold `n` decoupled from the
tree: if `n > 1` and `t` has at least `2n/3` leaves (`3 · |t| ≥ 2n`), then `t` has a subtree
`s` with `n/3 ≤ |s| < 2n/3` (`3 · |s| ≥ n` and `3 · |s| < 2n`). [RY20, Lemma 1.4 proof].

**Proof sketch.** Induction on `t`, walking down towards the heavier child.

1. A single leaf has one leaf, so `3 ≥ 2n` contradicts `n > 1`.
2. At a node, let `c` be the child with the larger leaf count (left if the counts tie); since
   the two children together hold at least `2n/3` leaves, `c` holds at least `n/3`.
3. If `c` holds fewer than `2n/3` leaves, `c` itself is the witness (it is a subtree via the
   corresponding `left`/`right` constructor).
4. Otherwise `c` holds at least `2n/3` leaves, so the induction hypothesis for `c` (with the
   same `n`) gives a witness inside `c`, which is a subtree of `t` by transitivity. -/
private lemma tree_balanced_subtree_aux (t : Tree α) (n : ℕ) (hn : 1 < n)
    (h : 3 * t.numLeaves ≥ 2 * n) :
    ∃ (s : Tree α), TreeIsSubtree s t ∧
      3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction t with
  | nil =>
    -- Step 1: a single leaf cannot hold `2n/3 > 1` leaves
    simp [Tree.numLeaves] at h; omega
  | node v l r ih_l ih_r =>
    -- Step 2: descend into the heavier child (left on ties)
    by_cases hl : l.numLeaves ≥ r.numLeaves
    · by_cases hlt : 3 * l.numLeaves < 2 * n
      · -- Step 3: the left child is the witness
        exact ⟨l, TreeIsSubtree.left v l l r (TreeIsSubtree.refl l),
               by simp [Tree.numLeaves] at h; omega, hlt⟩
      · -- Step 4: recurse into the left child and compose the subtree relation
        obtain ⟨s, hs, hlb, hub⟩ := ih_l (by omega)
        exact ⟨s, TreeIsSubtree.trans hs (TreeIsSubtree.left v l l r (TreeIsSubtree.refl l)),
               hlb, hub⟩
    · by_cases hlt : 3 * r.numLeaves < 2 * n
      · -- Step 3: the right child is the witness
        exact ⟨r, TreeIsSubtree.right v r l r (TreeIsSubtree.refl r),
               by simp [Tree.numLeaves] at h; omega, hlt⟩
      · -- Step 4: recurse into the right child and compose the subtree relation
        obtain ⟨s, hs, hlb, hub⟩ := ih_r (by omega)
        exact ⟨s, TreeIsSubtree.trans hs (TreeIsSubtree.right v r l r (TreeIsSubtree.refl r)),
               hlb, hub⟩

/-- Every binary tree `t` with `ℓ > 1` leaves has a subtree `s` (rooted at some vertex of
`t`) whose number of leaves `r` satisfies `ℓ/3 ≤ r < 2ℓ/3`, stated as `3r ≥ ℓ` and
`3r < 2ℓ`. [RY20, Lemma 1.4]. Deviation: the upper bound is strict (`r < 2ℓ/3` rather than
`r ≤ 2ℓ/3`), which is what the descent argument actually yields. The subtree relation
`TreeIsSubtree` is private to this file, so outside it the conclusion only exposes the
existence of `s` and its leaf-count bounds; the protocol-level consequence
`Subprotocol.balanced_subprotocol` re-proves the descent directly on protocols. -/
theorem tree_balanced_subtree (t : Tree α) (hn : 1 < t.numLeaves) :
    ∃ s : Tree α, TreeIsSubtree s t ∧ 3 * s.numLeaves ≥ t.numLeaves ∧
         3 * s.numLeaves < 2 * t.numLeaves :=
  -- The auxiliary lemma with `n := t.numLeaves`; its hypothesis `3 * n ≥ 2 * n` is trivial.
  tree_balanced_subtree_aux t t.numLeaves hn (by omega)

end CommunicationComplexity
