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

## Main results

- `Deterministic.Protocol.shape`: maps a protocol to its underlying binary tree shape
- `Deterministic.Protocol.numLeaves`: counts the number of output leaves in a protocol tree
- `tree_balanced_subtree`: every binary tree with more than one leaf has a subtree with between one third and two thirds of the total leaves

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

variable {X Y α : Type*}

namespace Deterministic.Protocol

def shape : Protocol X Y α → Tree Unit
| .output _  => .nil
| .alice _ P => .node () (shape (P false)) (shape (P true))
| .bob   _ P => .node () (shape (P false)) (shape (P true))

/-- The number of leaves (output nodes) in a protocol, defined via its tree shape. -/
def numLeaves (p : Protocol X Y α) : ℕ := p.shape.numLeaves

end Deterministic.Protocol

-- TreeIsSubtree: s is a subtree of t
-- Constructor args match Tree.node : α → Tree α → Tree α → Tree α
-- so .node v l r has v:α first, then children
private inductive TreeIsSubtree : Tree α → Tree α → Prop where
| refl  : ∀ (t : Tree α), TreeIsSubtree t t
| left  : ∀ (v : α) (s l r : Tree α), TreeIsSubtree s l → TreeIsSubtree s (.node v l r)
| right : ∀ (v : α) (s l r : Tree α), TreeIsSubtree s r → TreeIsSubtree s (.node v l r)

private lemma TreeIsSubtree.trans {s t u : Tree α} (h1 : TreeIsSubtree s t) (h2 : TreeIsSubtree t u) :
    TreeIsSubtree s u := by
  induction h2 with
  | refl _ => exact h1
  | left v s' l r hl ihl => exact TreeIsSubtree.left v s l r (ihl h1)
  | right v s' l r hr ihr => exact TreeIsSubtree.right v s l r (ihr h1)

private lemma tree_balanced_subtree_aux (t : Tree α) (n : ℕ) (hn : 1 < n)
    (h : 3 * t.numLeaves ≥ 2 * n) :
    ∃ (s : Tree α), TreeIsSubtree s t ∧
      3 * s.numLeaves ≥ n ∧ 3 * s.numLeaves < 2 * n := by
  induction t with
  | nil => simp [Tree.numLeaves] at h; omega
  | node v l r ih_l ih_r =>
    by_cases hl : l.numLeaves ≥ r.numLeaves
    · by_cases hlt : 3 * l.numLeaves < 2 * n
      · exact ⟨l, TreeIsSubtree.left v l l r (TreeIsSubtree.refl l),
               by simp [Tree.numLeaves] at h; omega, hlt⟩
      · obtain ⟨s, hs, hlb, hub⟩ := ih_l (by omega)
        exact ⟨s, TreeIsSubtree.trans hs (TreeIsSubtree.left v l l r (TreeIsSubtree.refl l)),
               hlb, hub⟩
    · by_cases hlt : 3 * r.numLeaves < 2 * n
      · exact ⟨r, TreeIsSubtree.right v r l r (TreeIsSubtree.refl r),
               by simp [Tree.numLeaves] at h; omega, hlt⟩
      · obtain ⟨s, hs, hlb, hub⟩ := ih_r (by omega)
        exact ⟨s, TreeIsSubtree.trans hs (TreeIsSubtree.right v r l r (TreeIsSubtree.refl r)),
               hlb, hub⟩

/-- Every binary tree with more than one leaf has a subtree with between one third and two thirds
of the total leaves. -/
theorem tree_balanced_subtree (t : Tree α) (hn : 1 < t.numLeaves) :
    ∃ s : Tree α, TreeIsSubtree s t ∧ 3 * s.numLeaves ≥ t.numLeaves ∧
         3 * s.numLeaves < 2 * t.numLeaves := by
  obtain ⟨v, l, r, rfl⟩ : ∃ v l r, t = Tree.node v l r := by
    match t with
    | .nil => simp [Tree.numLeaves] at hn
    | .node v l r => exact ⟨v, l, r, rfl⟩
  simp only [Tree.numLeaves] at *
  by_cases hl : l.numLeaves ≥ r.numLeaves
  · by_cases hlt : 3 * l.numLeaves < 2 * (l.numLeaves + r.numLeaves)
    · exact ⟨l, TreeIsSubtree.left v l l r (TreeIsSubtree.refl l), by omega, hlt⟩
    · obtain ⟨s, hs, hlb, hub⟩ :=
          tree_balanced_subtree_aux l (l.numLeaves + r.numLeaves) hn (by omega)
      exact ⟨s, TreeIsSubtree.trans hs (TreeIsSubtree.left v l l r (TreeIsSubtree.refl l)),
             hlb, hub⟩
  · by_cases hlt : 3 * r.numLeaves < 2 * (l.numLeaves + r.numLeaves)
    · exact ⟨r, TreeIsSubtree.right v r l r (TreeIsSubtree.refl r), by omega, hlt⟩
    · obtain ⟨s, hs, hlb, hub⟩ :=
          tree_balanced_subtree_aux r (l.numLeaves + r.numLeaves) hn (by omega)
      exact ⟨s, TreeIsSubtree.trans hs (TreeIsSubtree.right v r l r (TreeIsSubtree.refl r)),
             hlb, hub⟩

end CommunicationComplexity
