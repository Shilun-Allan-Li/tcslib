/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Planted

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reading nonabort as query safety

## Main definitions

None.

## Main results

* `safe_of_nonabort`: a nonaborting one-query planted transcript has a safe query.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, proof of Theorem 137.2.
-/

namespace TCSlib.Cryptography.Authentication.LamportFill

open TCSlib.Cryptography.Games

/-- A planted run with at most one query ending with a false abort bit queried no message
that reveals the planted cell [PS10, proof of Theorem 137.2].

**Proof sketch.** An immediate return has no query. A query leaves cost zero, so its
continuation is a return; the final abort flag is exactly equality of its selected bit with
the planted bit. A false flag therefore says that the query was safe. -/
theorem safe_of_nonabort {n : ℕ} {α : Type} (T : Table n) (i : Fin n) (c : Bool)
    (tree : OracleComp (bitSpec (fun _ : Fin 1 => n) (fun _ => n * n)) α)
    (hcost : tree.CostBoundedBy (fun _ => 1) 1) (a' : α)
    (hsim : simulate (abortingImpl T i c) tree false = .pure (a', false)) :
    Safe tree i c := by
  cases tree with
  | pure a =>
    apply (safe_iff _ i c).2
    intro m hm
    rw [firstQuery_pure] at hm
    cases hm
  | query j m k =>
    have hk := (OracleComp.costBoundedBy_query (fun _ => 1) j m k 1).1 hcost
    obtain ⟨a, ha⟩ := exists_pure_of_cost_zero (k (abortingAnswer T i c m))
      (by simpa only [Nat.sub_self] using (hk.2 (abortingAnswer T i c m)))
    rw [simulate_query, abortingImpl_apply, OracleComp.pure_bind, ha, simulate_pure] at hsim
    have hp : (a, false || decide (m i = c)) = (a', false) := OracleComp.pure.inj hsim
    have hb : decide (m i = c) = false := by
      simpa only [Bool.false_or] using congrArg Prod.snd hp
    have hm : m i ≠ c := of_decide_eq_false hb
    apply (safe_iff _ i c).2
    intro m' hm'
    rw [firstQuery_query, Option.some.injEq] at hm'
    rw [← hm']
    exact hm

end TCSlib.Cryptography.Authentication.LamportFill
