/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Replacing a fixed-width block in a concatenated tuple

## Main definitions

None.

## Main results

* `flatten_ofFn_update`: replacing a block by prefix, replacement and suffix agrees with a
  function update before serialization.

## References

Generic list and finite-tuple glue; no textbook counterpart.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

/-- Replacing block `i` of a concatenation of `B`-bit blocks by the `B`-bit word `h` is
serialization of the updated tuple:
`take(iB, flatten(g)) ++ h ++ drop((i+1)B, flatten(g)) = flatten(update(g,i,h))`.

**Proof sketch.** Induct on the number of blocks and split the updated index into zero or a
successor. At zero, dropping the first block leaves the unchanged tail. At a successor,
taking and dropping pass the initial block, so the induction hypothesis applies to the tail;
the untouched initial block is then prepended. All length calculations use the given uniform
block-width equations. -/
theorem flatten_ofFn_update {B : ℕ} :
    ∀ {q : ℕ} (g : Fin q → List Bool) (hg : ∀ j, (g j).length = B)
      (i : Fin q) (h : List Bool) (hh : h.length = B),
      (List.ofFn g).flatten.take (i.val * B) ++ h ++
          (List.ofFn g).flatten.drop ((i.val + 1) * B) =
        (List.ofFn (Function.update g i h)).flatten
  | 0, _, _, i, _, _ => i.elim0
  | q + 1, g, hg, i, h, hh => by
    have hflat : (List.ofFn g).flatten =
        g 0 ++ (List.ofFn (Fin.tail g)).flatten := by
      rw [List.ofFn_succ, List.flatten_cons]
    cases i using Fin.cases with
    | zero =>
      have hupdate : Function.update g 0 h = Fin.cons h (Fin.tail g) := by
        have hu := Fin.update_cons_zero (x := g 0) (p := Fin.tail g) (z := h)
        simpa only [Fin.cons_self_tail] using hu
      rw [hflat, hupdate, List.ofFn_cons, List.flatten_cons]
      simp only [Fin.val_zero, Nat.zero_mul, List.take_zero, List.nil_append,
        Nat.zero_add, Nat.one_mul]
      rw [List.drop_left' (hg 0)]
    | succ j =>
      have hstart : (j.succ : Fin (q + 1)).val * B = (g 0).length + j.val * B := by
        simp only [Fin.val_succ, hg 0]
        ring
      have hend : ((j.succ : Fin (q + 1)).val + 1) * B =
          (g 0).length + (j.val + 1) * B := by
        simp only [Fin.val_succ, hg 0]
        ring
      have hupdate : Function.update g j.succ h =
          Fin.cons (g 0) (Function.update (Fin.tail g) j h) := by
        rw [Fin.cons_update, Fin.cons_self_tail]
      rw [hflat, hstart, hend, List.take_length_add_append,
        List.drop_length_add_append, hupdate, List.ofFn_cons, List.flatten_cons]
      have ht : ∀ k : Fin q, ((Fin.tail g) k).length = B := fun k => hg k.succ
      simpa only [List.append_assoc] using congrArg (List.append (g 0))
        (flatten_ofFn_update (Fin.tail g) ht j h hh)

end TCSlib.Cryptography.Authentication.LamportFill
