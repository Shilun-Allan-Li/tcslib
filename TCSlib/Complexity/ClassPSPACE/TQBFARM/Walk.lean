/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Leaf

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The syntax check and the assignment walk of the `TQBF` register machine

The `TQBF` register machine `Complexity.LogProg.TQBFARM.A` first runs the syntax automaton
over its input (`syn_run`), then evaluates the quantified formula by a depth-first walk over
the partial assignments of its prefix, kept as a binary stack `S` at depth `K`. This file
holds the walk's building blocks — locating a node's pair (`node_run`), pushing (`push_run`),
popping (`pop_run`), the quantifier lookup (`qlook_run`) — and its correctness at a leaf
(`leaf_spec`), where the matrix is evaluated (`Complexity.LogProg.TQBFARM.formula_run`).
The inner nodes and the conclusion `TQBF ∈ PSPACE` are in
`TCSlib.Complexity.ClassPSPACE.TQBFARM.Correct`.

Infrastructure for [AB09, §4.2, Theorem 4.13, membership half]; not itself a result of the
book.

## Main definitions

* `Complexity.LogProg.TQBFARM.stp` — the register files of the walk.
* `Complexity.LogProg.TQBFARM.CallOK` — the correctness of the walk at a depth.

## Main results

* `Complexity.LogProg.TQBFARM.syn_run` — the syntax check.
* `Complexity.LogProg.TQBFARM.node_run`, `push_run`, `pop_run`, `qlook_run` — the walk's
  steps.
* `Complexity.LogProg.TQBFARM.leaf_spec` — the walk is correct at a leaf.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13.)
-/

namespace Complexity.LogProg

namespace TQBFARM

open Turing
open Std.Sat (CNF)

variable {x : List Bool} {B : ℕ}

/-! ## The syntax check -/

/-- **A length query answered `1`**. -/
lemma len_t {l l₁ l₀ : Lb} {st : St} {c : AConf 7 Lb}
    (hl : A l = .call 1 .whole [rP] l₁ l₀) (hbd : st.Bd B) (hp : st.P < x.length)
    (h : AReach A orc x (GuardLe A x B) (some l₁, st.toV, none) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c := by
  refine step_of hbd ?_
  simp only [astep, hl, vword_whole₁]
  rw [St.toV_P, orc_len, decide_eq_true hp, if_pos rfl]
  exact h

/-- **A length query answered `0`**. -/
lemma len_f {l l₁ l₀ : Lb} {st : St} {c : AConf 7 Lb}
    (hl : A l = .call 1 .whole [rP] l₁ l₀) (hbd : st.Bd B) (hp : ¬ st.P < x.length)
    (h : AReach A orc x (GuardLe A x B) (some l₀, st.toV, none) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c := by
  refine step_of hbd ?_
  simp only [astep, hl, vword_whole₁]
  rw [St.toV_P, orc_len, decide_eq_false hp, if_neg (by decide)]
  exact h

/-- **The syntax loop**: from `vl q` at `P = |x| - n`, the machine steps the automaton over the
rest of the input and reaches `vend q'` at `P = |x|`.

**Proof sketch.** Induction on `n`: below the end, the length query succeeds, the bit is read
and the automaton stepped; at the end the query fails. -/
theorem syn_run : ∀ (n : ℕ) (q : SynSt) (st : St), st.P + n = x.length → st.Bd B →
    x.length ≤ B →
    Run x B (.vl q) st (.vend ((x.drop st.P).foldl synStep q)) { st with P := x.length } := by
  intro n
  induction n with
  | zero =>
    intro q st hn hbd hx
    refine len_f (l := .vl q) rfl hbd (by omega) ?_
    rw [List.drop_eq_nil_of_le (by omega), List.foldl_nil]
    exact fin_of (by sext)
  | succ n ih =>
    intro q st hn hbd hx
    have hlt : st.P < x.length := by omega
    have hd : x.drop st.P = x[st.P] :: x.drop (st.P + 1) := List.drop_eq_getElem_cons hlt
    generalize x[st.P] = b at hd
    have hbd1 : St.Bd B { st with P := st.P + 1 } := by bdt
    have := ih (synStep q b) { st with P := st.P + 1 } (by simp; omega) hbd1 hx
    refine len_t (l := .vl q) rfl hbd hlt ?_
    refine read_b (l := .vr q) rfl hbd (getD_of_drop hd) ?_
    rw [hd, List.foldl_cons]
    cases b <;>
    · refine step_of hbd ?_
      regs [astep, A, cond_true, cond_false]
      exact this

/-! ## The walk -/

/-- **The register file of the walk** at depth `k`, with stack `S` and pointer `p`: every
other register clear. -/
def stp (k S p : ℕ) : St := ⟨k, S, p, 0, 0, 0, 0⟩

/-- Continue a run from an equal register file. -/
lemma cont {st st' : St} {l : Lb} {c : AConf 7 Lb} (e : st = st')
    (h : AReach A orc x (GuardLe A x B) (some l, st'.toV, none) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c := e ▸ h

/-- A walk register file is bounded. -/
lemma stp_bd {k S p : ℕ} (hk : k ≤ B) (hS : S ≤ B) (hp : p ≤ B) : (stp k S p).Bd B := by
  simp only [St.Bd, stp]; omega

section Walk

variable {qs : List Bool} {φ : CNF ℕ}

/-- The bits of an encoded formula: the doubled prefix, then the separator `01`. -/
lemma getD_enc (hx : x = pairEncode qs (CNF.serialize φ)) (j : ℕ) :
    x.getD j false = if j < 2 * qs.length then qs.getD (j / 2) false
      else if j = 2 * qs.length then false
      else if j = 2 * qs.length + 1 then true
      else (CNF.serialize φ).getD (j - 2 * qs.length - 2) false := by
  rw [hx, pairEncode_getD]

/-- The length of an encoded formula: at least `2|qs| + 2`. -/
lemma length_enc (hx : x = pairEncode qs (CNF.serialize φ)) : 2 * qs.length + 2 ≤ x.length := by
  rw [hx, length_pairEncode]; omega

/-- **Locating the node's pair**: from `node`, the machine sets `P := 2K` and reaches `nd1`. -/
theorem node_run (k S p : ℕ) (hk : 2 * k ≤ B) (hS : S ≤ B) (hp : p ≤ B) :
    Run x B .node (stp k S p) .nd1 (stp k S (2 * k)) := by
  refine step_of (stp_bd (by omega) hS hp) ?_
  regs [astep, A]
  refine cont (st' := stp k S 0) rfl ?_
  refine (cp_run .ndA _ (stp_bd (by omega) hS (by omega)) rfl
    (by simp only [cpDst, cpSrc]; regs; simp [stp]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit]
  refine cont (st' := stp k S k) (by sext [stp]) ?_
  refine (cp_run .ndB _ (stp_bd (by omega) hS (by omega)) rfl
    (by simp only [cpDst, cpSrc]; regs; simp [stp]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit]
  exact fin_of (by sext [stp])

/-- **A push**: from `push b` at depth `k` with stack `S` (any pointer), the machine reaches
`node` at depth `k + 1` with stack `2S + b`.

**Proof sketch.** Straight-line code: clear `P`; the doubled move (`dm_run`) gives `T = 2S`,
`S = 0`; the move back (`mv_run`) gives `S = 2S`, `T = 0`; for `b = 1` increment `S`; then
increment `K`. Each step keeps the registers below `B` (`stp_bd`). -/
theorem push_run (b : Bool) (k S p : ℕ) (hp : p ≤ B) (hS : 2 * S + 1 ≤ B) (hk : k + 1 ≤ B) :
    Run x B (.push b) (stp k S p) .node (stp (k + 1) (2 * S + b.toNat) 0) := by
  refine step_of (stp_bd (by omega) (by omega) hp) ?_
  regs [astep, A]
  refine cont (st' := stp k S 0) rfl ?_
  refine (dm_run b _ (stp_bd (by omega) (by omega) (by omega)) (by simp [stp]; omega)).trans ?_
  refine cont (st' := ⟨k, 0, 0, 2 * S, 0, 0, 0⟩) (by sext [stp]) ?_
  refine (mv_run b _ (by simp only [St.Bd]; omega) (by simp; omega)).trans ?_
  refine cont (st' := ⟨k, 2 * S, 0, 0, 0, 0, 0⟩) (by sext) ?_
  cases b
  · simp only [Bool.false_eq_true, if_false]
    refine step_of (by simp only [St.Bd]; omega) ?_
    regs [astep, A]
    exact fin_of (by sext [stp])
  · simp only [if_true]
    refine step_of (by simp only [St.Bd]; omega) ?_
    regs [astep, A]
    refine step_of (by simp only [St.Bd]; omega) ?_
    regs [astep, A]
    exact fin_of (by sext [stp])

/-- **A pop**: from `rt v` at depth `k + 1` with stack `2S + b`, the machine returns to depth
`k` with stack `S`, at `rt v` after a second child (`b = 1`) and at the quantifier lookup after
a first child.

**Proof sketch.** Straight-line code: `K = k + 1 ≠ 0`, so `rt v` decrements `K`; the parity
test of `S = 2S + b` branches on `b`, and both branches halve `S` (`(2S + b) / 2 = S`), going
on to `rt v` (`b = 1`) or to the quantifier lookup (`b = 0`). -/
theorem pop_run (v b : Bool) (k S : ℕ) (hk : k + 1 ≤ B) (hS : 2 * S + 1 ≤ B) :
    Run x B (.rt v) (stp (k + 1) (2 * S + b.toNat) 0) (cond b (.rt v) (.cp (.qA v) 0))
      (stp k S 0) := by
  have hb : b.toNat ≤ 1 := Bool.toNat_le b
  refine step_of (stp_bd hk (by omega) (by omega)) ?_
  regs [astep, A]
  simp only [stp, Nat.add_one_ne_zero, if_false]
  refine step_of (stp_bd hk (by omega) (by omega)) ?_
  regs [astep, A]
  refine cont (st' := stp k (2 * S + b.toNat) 0) (by sext [stp]) ?_
  refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
  regs [astep, A]
  have h2 : (2 * S + b.toNat) / 2 = S := by omega
  cases b
  · simp only [stp, Bool.toNat_false, add_zero, Nat.mul_mod_right, zero_ne_one, if_false]
    refine step_of (stp_bd (B := B) (k := k) (S := 2 * S) (p := 0) (by omega) (by omega)
      (by omega)) ?_
    regs [astep, A]
    exact fin_of (by sext [stp])
  · simp only [stp, Bool.toNat_true, Nat.mul_add_mod, Nat.one_mod, if_true]
    refine step_of (stp_bd (B := B) (k := k) (S := 2 * S + 1) (p := 0) (by omega) (by omega)
      (by omega)) ?_
    regs [astep, A]
    exact fin_of (by sext [stp])

/-- **The quantifier lookup**: from `cp (qA v) 0` at depth `k`, the machine sets `P := 2K` and
reaches `qr v`. -/
theorem qlook_run (v : Bool) (k S : ℕ) (hk : 2 * k ≤ B) (hS : S ≤ B) :
    Run x B (.cp (.qA v) 0) (stp k S 0) (.qr v) (stp k S (2 * k)) := by
  refine (cp_run (.qA v) _ (stp_bd (by omega) hS (by omega)) rfl
    (by simp only [cpDst, cpSrc]; regs; simp [stp]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit]
  refine cont (st' := stp k S k) (by sext [stp]) ?_
  refine (cp_run (.qB v) _ (stp_bd (by omega) hS (by omega)) rfl
    (by simp only [cpDst, cpSrc]; regs; simp [stp]; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit]
  exact fin_of (by sext [stp])

variable (x B qs φ) in
open Classical in
/-- **The walk is correct at depth `k`**: from `node` at depth `k` with any stack `S` below
`2 ^ (k + 1)`, the machine reaches `rt v` with the same registers, `v` the value
`Val qs φ k S`. -/
def CallOK (k : ℕ) : Prop :=
  ∀ S, S < 2 ^ (k + 1) →
    Run x B .node (stp k S 0) (.rt (decide (Val qs φ k S))) (stp k S 0)

open Classical in
/-- **A leaf**: at depth `|qs|` the walk returns the value of the matrix.

**Proof sketch.** The pair at `2K` is the separator: bit `2K` is `0`, bit `2K + 1` is `1`;
the matrix starts at `2K + 2` (`formula_run`), and `val_leaf` identifies its value. -/
theorem leaf_spec (hx : x = pairEncode qs (CNF.serialize φ)) (hB1 : 2 ^ (qs.length + 1) ≤ B)
    (hB2 : x.length ≤ B) : CallOK x B qs φ qs.length := by
  intro S hS
  have hlen := length_enc hx
  set M := qs.length with hM
  refine (node_run M S 0 (by omega) (by omega) (by omega)).trans ?_
  refine read_f (l := .nd1) rfl (stp_bd (by omega) (by omega) (by omega))
    (by show x.getD (2 * M) false = false; rw [getD_enc hx, ← hM]; simp) ?_
  refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
  regs [astep, A]
  refine cont (st' := stp M S (2 * M + 1)) rfl ?_
  refine read_t (l := .nd3) rfl (stp_bd (by omega) (by omega) (by omega))
    (by show x.getD (2 * M + 1) false = true; rw [getD_enc hx, ← hM]; simp) ?_
  refine step_of (stp_bd (by omega) (by omega) (by omega)) ?_
  regs [astep, A]
  refine cont (st' := stp M S (2 * M + 2)) rfl ?_
  have hd : x.drop (stp M S (2 * M + 2)).P = CNF.serialize φ ++ [] := by
    rw [hx]; simp [stp, pairEncode_eq_dbl, List.drop_append, hM]
  have := formula_run [] φ (stp M S (2 * M + 2)) hd (stp_bd (by omega) (by omega) (by omega))
    hB2 rfl rfl rfl rfl
  have hv : decide (Val qs φ M S) = CNF.eval (asg M S) φ := by
    rw [hM, Bool.eq_iff_iff, decide_eq_true_iff, val_leaf]
  rw [hv]
  exact reach_of_eq this (by congr 3)

end Walk

end TQBFARM

end Complexity.LogProg
