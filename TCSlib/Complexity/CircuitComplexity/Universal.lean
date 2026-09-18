/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange
import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Universality: every Boolean function is computed by a circuit

[AB09, Claim 2.13], in the form [AB09, p.108] cites it in Chapter 6: every
`f : (Fin n → Bool) → Bool` is computed by a `BoolCircuit.Circuit n` of
explicitly bounded size.

## Main definitions

* `ACP.minterm v` — the `AND` of `n` literals that is true exactly at `v`.
* `ACP.universalCircuit f` — the `OR` of the minterms of `f`'s satisfying
  assignments.

## Main results

* `ACP.universalCircuit_eval` — `universalCircuit f` computes `f`.
* `ACP.universalCircuit_size` — its size is exactly `(n + 1)` times the number
  of satisfying assignments, plus one.
* `ACP.universalCircuit_size_le` — hence at most `2 ^ n * (n + 1) + 1`, a bound
  `ACP.universalCircuit_const_true_size` shows is attained.
* `ACP.exists_circuit_eval_eq_size_le` — the headline existence statement.

## Divergences from [AB09, Claim 2.13]

AB builds the **CNF** `⋀_{v : f v = 0} C_v` over the *falsifying* assignments;
we build the dual **DNF** `⋁_{v : f v = 1} T_v` over the satisfying ones.  Both
are one gate over at most `2ⁿ` gates of `n` literals; only the DNF is formalized
here.

**The constant is ours, not AB's.**  AB quotes `n2ⁿ`, which is Claim 2.13's
count of `∧`/`∨` *symbols*, whereas [AB09, Def 6.1] sizes a circuit by its
*vertex* count on a fan-in-2 DAG whose `n` sources are shared.  `Circuit.size`
counts every node of an unbounded-fan-in *tree*, literal leaves included, and a
variable read `k` times contributes `k` leaves.  What this construction actually
gives is therefore `2 ^ n * (n + 1) + 1` — the same order as `n2ⁿ`, a larger
number — and that is what is proved here.  [AB09, Ex 6.1]'s sharper `O(2ⁿ/n)` is
a different construction and is not attempted.

`Formulas.lean`'s `DNF` is not used as the intermediate: it is built on
`Literal`, a type distinct from `Basic.lean`'s `Lit`; it carries no size measure;
and TCSlib has no `DNF → Circuit` map (`NOrCircuit.toDNF` and `depth2OrToDNF`
both run the other way).  Using it would mean adding both.  `universalCircuit`
is `noncomputable` only because `Finset.toList` is.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

open BoolCircuit

namespace ACP

variable {n : ℕ}

/-- The literal `⟨i, b⟩` holds at `x` exactly when `x i = b`. -/
private theorem lit_eval_iff (i : Fin n) (b : Bool) (x : Fin n → Bool) :
    (Lit.eval ⟨i, b⟩ x) = true ↔ x i = b := by
  cases b <;> simp [Lit.eval]

/-- Summed size of `l.map g` when every `g a` has size `k`. -/
private theorem foldr_size_map {α : Type*} {k : ℕ} (g : α → Circuit n)
    (hg : ∀ a, (g a).size = k) (l : List α) :
    (l.map g).foldr (fun c acc => c.size + acc) 0 = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.foldr_cons, ih, hg a, List.length_cons]; ring

/-- The minterm of `v`: the `AND` over all `n` variables of the literal that `v`
satisfies.  At `n = 0` this is the empty conjunction. -/
def minterm (v : Fin n → Bool) : Circuit n :=
  .node true ((List.finRange n).map fun i => .lit ⟨i, v i⟩)

/-- `minterm v` accepts `v` and nothing else. -/
theorem minterm_eval_iff (v x : Fin n → Bool) :
    (minterm v).eval x = true ↔ x = v := by
  rw [minterm, Circuit.eval_node_true_iff]
  constructor
  · intro h
    funext i
    have hi := h (.lit ⟨i, v i⟩) (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
    rw [Circuit.eval_lit] at hi
    exact (lit_eval_iff i (v i) x).mp hi
  · rintro rfl c hc
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    rw [Circuit.eval_lit]
    exact (lit_eval_iff i (x i) x).mpr rfl

/-- A minterm is one gate over `n` leaves. -/
theorem minterm_size (v : Fin n → Bool) : (minterm v).size = n + 1 := by
  rw [minterm, Circuit.size, foldr_size_map _ (fun _ => by simp [Circuit.size]) (k := 1),
    List.length_finRange]
  ring

/-- The DNF of `f` as a circuit: the `OR` of the minterms of `f`'s satisfying
assignments.  [AB09, Claim 2.13] -/
noncomputable def universalCircuit (f : (Fin n → Bool) → Bool) : Circuit n :=
  .node false ((Finset.univ.filter fun v => f v = true).toList.map minterm)

/-- `universalCircuit f` computes `f`. -/
theorem universalCircuit_eval (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    (universalCircuit f).eval x = f x := by
  rw [Bool.eq_iff_iff, universalCircuit, Circuit.eval_node_false_iff]
  constructor
  · rintro ⟨c, hc, hce⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    rw [(minterm_eval_iff v x).mp hce]
    simpa using Finset.mem_toList.mp hv
  · intro hx
    exact ⟨minterm x, List.mem_map.mpr ⟨x, Finset.mem_toList.mpr (by simpa using hx), rfl⟩,
      (minterm_eval_iff x x).mpr rfl⟩

/-- One `OR` gate over one `(n + 1)`-node minterm per satisfying assignment. -/
theorem universalCircuit_size (f : (Fin n → Bool) → Bool) :
    (universalCircuit f).size
      = (Finset.univ.filter fun v => f v = true).card * (n + 1) + 1 := by
  rw [universalCircuit, Circuit.size, foldr_size_map minterm minterm_size,
    Finset.length_toList]
  ring

/-- The size bound: `2 ^ n * (n + 1) + 1`, this construction's own constant. -/
theorem universalCircuit_size_le (f : (Fin n → Bool) → Bool) :
    (universalCircuit f).size ≤ 2 ^ n * (n + 1) + 1 := by
  rw [universalCircuit_size]
  refine Nat.add_le_add_right (Nat.mul_le_mul_right _ ?_) 1
  calc (Finset.univ.filter fun v => f v = true).card
      ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

/-- Every Boolean function on `n` bits is computed by a circuit of size at most
`2 ^ n * (n + 1) + 1`.  [AB09, Claim 2.13], as cited at [AB09, p.108] -/
theorem exists_circuit_eval_eq_size_le (f : (Fin n → Bool) → Bool) :
    ∃ c : Circuit n, (∀ x, c.eval x = f x) ∧ c.size ≤ 2 ^ n * (n + 1) + 1 :=
  ⟨universalCircuit f, universalCircuit_eval f, universalCircuit_size_le f⟩

/-! ### Degenerate cases -/

/-- No satisfying assignment: the circuit is the empty `OR`. -/
theorem universalCircuit_const_false :
    universalCircuit (fun _ : Fin n → Bool => false) = .node false [] := by
  simp [universalCircuit]

/-- Every assignment satisfying: the bound is attained. -/
theorem universalCircuit_const_true_size :
    (universalCircuit (fun _ : Fin n → Bool => true)).size = 2 ^ n * (n + 1) + 1 := by
  rw [universalCircuit_size]
  simp

/-- At `n = 0` a minterm is the empty conjunction, hence constantly `true`. -/
theorem minterm_eval_zero (v x : Fin 0 → Bool) : (minterm v).eval x = true :=
  (minterm_eval_iff v x).mpr (funext fun i => i.elim0)

end ACP
