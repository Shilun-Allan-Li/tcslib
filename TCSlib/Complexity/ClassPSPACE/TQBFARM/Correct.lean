/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Walk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# True quantified Boolean formulas are decidable in polynomial space

The correctness of the assignment walk of the `TQBF` register machine
`Complexity.LogProg.TQBFARM.A` at an inner node (`inner_spec`), hence at every depth
(`call_spec`), and the resulting membership of the true quantified Boolean formulas in
`PSPACE` (`Complexity.LogProg.TQBFARM.truth_mem_PSPACE`) — the membership half of
[AB09, Theorem 4.13], by the recursive evaluation of its proof run with an explicit stack
of assignment bits.

## Main results

* `Complexity.LogProg.TQBFARM.inner_spec`, `Complexity.LogProg.TQBFARM.call_spec` — the
  walk computes `Complexity.LogProg.TQBFARM.Val`.
* `Complexity.LogProg.TQBFARM.truth_mem_PSPACE` — `{x | (QBF.decode x).truth} ∈ PSPACE`.
  [AB09, Theorem 4.13, membership half]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13.)
-/

namespace Complexity.LogProg

namespace TQBFARM

open Turing
open Std.Sat (CNF)

variable {x : List Bool} {B : ℕ} {qs : List Bool} {φ : CNF ℕ}

/-- The prefix bit `k` sits doubled at input positions `2k` and `2k + 1`. -/
lemma getD_quant (hx : x = pairEncode qs (CNF.serialize φ)) {k : ℕ} (hk : k < qs.length) :
    x.getD (2 * k) false = qs[k] ∧ x.getD (2 * k + 1) false = qs[k] := by
  rw [getD_enc hx, getD_enc hx]
  simp [show 2 * k < 2 * qs.length by omega, show 2 * k + 1 < 2 * qs.length by omega,
    show (2 * k + 1) / 2 = k by omega, hk]

open Classical in
/-- **An inner node**: if the walk is correct at depth `k + 1 ≤ |qs|`, it is correct at
depth `k`.

**Proof sketch.** The node reads the prefix bit at `2K` (and, when it is `0`, the bit at
`2K + 1`, again not the separator) and pushes `0`; the first child returns
`v₀ = Val (k + 1) (2S)` (the hypothesis), the pop restores `S` and the quantifier is read
again at `2K`. If `v₀` decides the quantifier (`1` under `∃`, `0` under `∀`) the node returns
`v₀`; otherwise it pushes `1`, and the second child's value `Val (k + 1) (2S + 1)` is returned
after the pop. `val_ex` and `val_all` identify the returned value with `Val k S`. -/
theorem inner_spec (hx : x = pairEncode qs (CNF.serialize φ)) (hB1 : 2 ^ (qs.length + 1) ≤ B)
    (hB2 : x.length ≤ B) (k : ℕ) (hk : k < qs.length) (IH : CallOK x B qs φ (k + 1)) :
    CallOK x B qs φ k := by
  intro S hS
  have hlen := length_enc hx
  obtain ⟨hq0, hq1⟩ := getD_quant hx hk
  have hp1 : 2 ^ (k + 2) ≤ 2 ^ (qs.length + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hp2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; ring
  have hS2 : 2 * S + 1 ≤ B := by omega
  have hkB : 2 * k + 1 ≤ B := by omega
  -- the first child
  have first : Run x B .node (stp k S 0) .node (stp (k + 1) (2 * S) 0) := by
    refine (node_run k S 0 (by omega) (by omega) (by omega)).trans ?_
    have e : stp (k + 1) (2 * S) 0 = stp (k + 1) (2 * S + false.toNat) 0 := by simp
    rw [e]
    cases hqk : qs[k]
    · refine read_f (l := .nd1) rfl (stp_bd (by omega) (by omega) (by omega))
        (by show x.getD (2 * k) false = false; rw [hq0, hqk]) ?_
      refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
      regs [astep, A]
      refine cont (st' := stp k S (2 * k + 1)) rfl ?_
      refine read_f (l := .nd3) rfl (stp_bd (by omega) (by omega) (by omega))
        (by show x.getD (2 * k + 1) false = false; rw [hq1, hqk]) ?_
      exact push_run false k S _ (by omega) hS2 (by omega)
    · refine read_t (l := .nd1) rfl (stp_bd (by omega) (by omega) (by omega))
        (by show x.getD (2 * k) false = true; rw [hq0, hqk]) ?_
      exact push_run false k S _ (by omega) hS2 (by omega)
  have c0 := IH (2 * S) (by omega)
  -- the pop after the first child and the quantifier lookup
  have back : ∀ v : Bool, Run x B (.rt v) (stp (k + 1) (2 * S) 0) (cond qs[k] (.qE v) (.qU v))
      (stp k S (2 * k)) := by
    intro v
    have hp := pop_run (x := x) v false k S (by omega) hS2
    simp only [Bool.toNat_false, add_zero, cond_false] at hp
    refine hp.trans ((qlook_run v k S (by omega) (by omega)).trans ?_)
    exact read_b (l := .qr v) rfl (stp_bd (by omega) (by omega) (by omega)) hq0 (AReach.refl _)
  -- the second child, entered from a push of `1`
  have second : Run x B (.push true) (stp k S 0) (.rt (decide (Val qs φ (k + 1) (2 * S + 1))))
      (stp k S 0) := by
    have hpush := push_run (x := x) true k S 0 (by omega) hS2 (by omega)
    simp only [Bool.toNat_true] at hpush
    refine hpush.trans ((IH (2 * S + 1) (by omega)).trans ?_)
    have hp := pop_run (x := x) (decide (Val qs φ (k + 1) (2 * S + 1))) true k S (by omega) hS2
    simpa only [Bool.toNat_true, cond_true] using hp
  refine first.trans (c0.trans ((back _).trans ?_))
  by_cases h0 : Val qs φ (k + 1) (2 * S)
  · rw [decide_eq_true h0]
    cases hqk : qs[k]
    · -- universal, first child true: the second child decides
      have hv : Val qs φ k S ↔ Val qs φ (k + 1) (2 * S + 1) := by
        rw [val_all qs φ k S hk hqk]; exact ⟨fun h => h.2, fun h => ⟨h0, h⟩⟩
      refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
      regs [astep, A, cond_false, if_true]
      refine cont (st' := stp k S 0) rfl ?_
      rw [show decide (Val qs φ k S) = decide (Val qs φ (k + 1) (2 * S + 1)) from
        decide_eq_decide.mpr hv]
      exact second
    · -- existential, first child true
      have hv : Val qs φ k S := (val_ex qs φ k S hk hqk).mpr (Or.inl h0)
      refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
      regs [astep, A, cond_true, if_true]
      rw [decide_eq_true hv]
      exact fin_of (by sext [stp])
  · rw [decide_eq_false h0]
    cases hqk : qs[k]
    · -- universal, first child false
      have hv : ¬ Val qs φ k S := fun h => h0 ((val_all qs φ k S hk hqk).mp h).1
      refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
      regs [astep, A, cond_false, Bool.false_eq_true, if_false]
      rw [decide_eq_false hv]
      exact fin_of (by sext [stp])
    · -- existential, first child false: the second child decides
      have hv : Val qs φ k S ↔ Val qs φ (k + 1) (2 * S + 1) := by
        rw [val_ex qs φ k S hk hqk]; exact ⟨fun h => h.resolve_left h0, Or.inr⟩
      refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
      regs [astep, A, cond_true, Bool.false_eq_true, if_false]
      refine cont (st' := stp k S 0) rfl ?_
      rw [show decide (Val qs φ k S) = decide (Val qs φ (k + 1) (2 * S + 1)) from
        decide_eq_decide.mpr hv]
      exact second

/-- **The walk is correct at every depth.**

**Proof sketch.** Induction on the remaining depth `|qs| - k`: `leaf_spec` at the full depth,
`inner_spec` above. -/
theorem call_spec (hx : x = pairEncode qs (CNF.serialize φ)) (hB1 : 2 ^ (qs.length + 1) ≤ B)
    (hB2 : x.length ≤ B) : ∀ j k, k + j = qs.length → CallOK x B qs φ k := by
  intro j
  induction j with
  | zero =>
    intro k hk
    obtain rfl : k = qs.length := by omega
    exact leaf_spec hx hB1 hB2
  | succ j ih =>
    intro k hk
    exact inner_spec hx hB1 hB2 k (by omega) (ih (k + 1) (by omega))

open Classical in
/-- **True quantified Boolean formulas are decidable in polynomial space**: the strings whose
decoding (`Complexity.QBF.decode`) is a true formula form a language in `PSPACE`.
[AB09, Theorem 4.13, membership half]

**Proof sketch.** `Complexity.LogProg.arm_decides_pspace_val` with the input-bit and
input-length deciders and the value bound `2 ^ (|x| + 1)`. The machine sets `S := 1` and runs
the syntax automaton over `x` (`syn_run`). A rejected string decodes to a true formula
(`truth_of_not_synOK`), and the machine answers `1`. An accepted string is
`pairEncode qs (serialize φ)` (`repr_of_synOK`); the walk from the root returns
`Val qs φ 0 1` (`call_spec`), the truth of the decoded formula (`val_root`). Every register
stays at most `2 ^ (|qs| + 1) ≤ 2 ^ (|x| + 1)`: the stack has at most `|qs| + 1` binary
digits and the pointer, depth and counters are at most `|x|`. -/
theorem truth_mem_PSPACE : {x : List Bool | (QBF.decode x).truth} ∈ PSPACE := by
  refine arm_decides_pspace_val A .init decs (fun j => LOGSPACE_subset_PSPACE (decs_mem j)) 1 1
    fun x => ?_
  set B := 2 ^ (1 * (x.length + 1) ^ 1) with hB
  have hB' : B = 2 ^ (x.length + 1) := by simp [hB]
  have hxB : x.length + 1 ≤ B := by rw [hB']; exact (Nat.lt_two_pow_self).le
  change AHalt A orc x (GuardLe A x B) (some .init, fun _ => 0, none) _
  rw [St.toV_zero]
  refine AHalt.step (gb_of (by simp only [St.Bd, St.zero]; omega) .init) ?_
  regs [astep, A]
  have hbd1 : St.Bd B { St.zero with S := 0 + 1 } := by simp only [St.Bd, St.zero]; omega
  refine (syn_run (x := x) (B := B) x.length (.inl none) { St.zero with S := 0 + 1 }
    (by simp [St.zero]) hbd1 (by omega)).halt ?_
  simp only [St.zero, List.drop_zero]
  rw [indicator_eq_decide]
  by_cases hv : synOK x = true
  · obtain ⟨qs, φ, hx⟩ := repr_of_synOK hv
    have hq : x.foldl synStep (.inl none) = .inr 4 := by simpa [synOK] using hv
    rw [hq]
    have hlen := length_enc hx
    have hB1 : 2 ^ (qs.length + 1) ≤ B := by
      rw [hB']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
    refine AHalt.step (gb_of (by simp only [St.Bd]; omega) _) ?_
    regs [astep, A, if_true]
    refine AReach.halt (b := (some (.rt (decide (Val qs φ 0 1))), (stp 0 1 0).toV, none))
      (reach_of_eq ((cont (st' := stp 0 1 0) (by sext [stp]) (call_spec hx hB1 (by omega)
        qs.length 0 (by omega) 1 (by norm_num)))) rfl) ?_
    refine AHalt.step (gb_of (stp_bd (by omega) (by omega) (by omega)) _) ?_
    simp only [astep, A, stp, St.toV_K]
    regs [if_true]
    have hans : decide (Val qs φ 0 1) = decide (x ∈ {x : List Bool | (QBF.decode x).truth}) := by
      apply decide_eq_decide.mpr
      rw [val_root, ← hx]; rfl
    rw [hans]
    exact AHalt.ret rfl (gb_of (stp_bd (by omega) (by omega) (by omega)) _)
  · have hf : synOK x = false := by simpa using hv
    have hq : x.foldl synStep (.inl none) ≠ .inr 4 := by simpa [synOK] using hf
    have hmem : decide (x ∈ {x : List Bool | (QBF.decode x).truth}) = true :=
      decide_eq_true (truth_of_not_synOK hf)
    rw [hmem]
    exact AHalt.ret (by simp [A, hq]) (gb_of (by simp only [St.Bd]; omega) _)

end TQBFARM

end Complexity.LogProg
