/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFARM.Machine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Matrix evaluation in the `TQBF` register machine

At a leaf of the assignment walk, `Complexity.LogProg.TQBFARM.A` evaluates the CNF matrix
under the assignment `Complexity.LogProg.TQBFARM.asg K S` of its stack, streaming the
serialization `Std.Sat.CNF.serialize` from the input: a literal `(v, b)` is a unary run of
`v + 1` ones, a zero and the polarity bit (`lc_run`, `lit_run`); a clause is a list of
literals closed by a zero (`clause_run`); the formula is a list of clauses, each announced by
a one, closed by a zero (`formula_run`). The variable's value is read off the stack by the
arithmetic of `lv_run`. Every run is through register files bounded by `B`.

Infrastructure for [AB09, §4.2, Theorem 4.13, membership half]; not itself a result of the
book.

## Main definitions

* none (run theorems of the input reads and the matrix evaluation; the file also adds the
  scoped tactics `bdt` and `sext`, which close register-file bounds and register-file
  equations).

## Main results

* `Complexity.LogProg.TQBFARM.read_t`, `read_f` — a read of the input.
* `Complexity.LogProg.TQBFARM.lv_run` — the lookup of a literal's variable.
* `Complexity.LogProg.TQBFARM.formula_run` — the matrix evaluation.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13.)
-/

namespace Complexity.LogProg

namespace TQBFARM

open Turing
open Std.Sat (CNF)

/-! ## Reading the input -/

variable {x : List Bool} {B : ℕ}

/-- **A read of the input returning `1`**: a bit call at a label continues at its yes-label. -/
lemma read_t {l l₁ l₀ : Lb} {st : St} {c : AConf 7 Lb}
    (hl : A l = .call 0 .whole [rP] l₁ l₀) (hbd : st.Bd B) (hb : x.getD st.P false = true)
    (h : AReach A orc x (GuardLe A x B) (some l₁, st.toV, none) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c := by
  refine step_of hbd ?_
  simp only [astep, hl, vword_whole₁]
  rw [St.toV_P, orc_bit, hb, if_pos rfl]
  exact h

/-- **A read of the input returning `0`**: a bit call at a label continues at its no-label. -/
lemma read_f {l l₁ l₀ : Lb} {st : St} {c : AConf 7 Lb}
    (hl : A l = .call 0 .whole [rP] l₁ l₀) (hbd : st.Bd B) (hb : x.getD st.P false = false)
    (h : AReach A orc x (GuardLe A x B) (some l₀, st.toV, none) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c := by
  refine step_of hbd ?_
  simp only [astep, hl, vword_whole₁]
  rw [St.toV_P, orc_bit, hb, if_neg (by decide)]
  exact h

/-- **A read of the input**, by the value read. -/
lemma read_b {l l₁ l₀ : Lb} {st : St} {c : AConf 7 Lb}
    (hl : A l = .call 0 .whole [rP] l₁ l₀) (hbd : st.Bd B) {b : Bool}
    (hb : x.getD st.P false = b)
    (h : AReach A orc x (GuardLe A x B) (some (cond b l₁ l₀), st.toV, none) c) :
    AReach A orc x (GuardLe A x B) (some l, st.toV, none) c := by
  cases b
  · exact read_f hl hbd hb h
  · exact read_t hl hbd hb h

/-- Close a register-file bound from the unfolded bounds in context. -/
scoped macro "bdt" : tactic => `(tactic| (simp only [St.Bd] at *; omega))

/-- Close an equation of register files field by field. -/
scoped syntax "sext" (" [" (Lean.Parser.Tactic.simpLemma),* "]")? : tactic
scoped macro_rules
  | `(tactic| sext) => `(tactic| (ext <;> (try simp) <;> omega))
  | `(tactic| sext [$args,*]) => `(tactic| (ext <;> (try simp [$args,*]) <;> omega))

/-! ## Literals -/

/-- **Counting a unary variable**: from `lc s` with the input at `P` reading `1ⁿ 0 b`, the
machine adds `n` to `V`, moves `P` past the polarity and reaches `lv s b`.

**Proof sketch.** Induction on `n`: each `1` increments `V` and `P`; the final zero and the
polarity bit are read and skipped. -/
theorem lc_run (s b : Bool) (rest : List Bool) : ∀ (n : ℕ) (st : St),
    x.drop st.P = List.replicate n true ++ false :: b :: rest → st.Bd B →
    x.length ≤ B → st.V ≤ st.P →
    Run x B (.lc s) st (.lv s b) { st with P := st.P + n + 2, V := st.V + n } := by
  intro n
  induction n with
  | zero =>
    intro st h hbd hx hV
    simp only [List.replicate_zero, List.nil_append] at h
    have h1 := drop_succ_of_drop h
    have hl := lt_of_drop h1
    refine read_f (l := .lc s) rfl hbd (getD_of_drop h) ?_
    refine step_of hbd ?_
    regs [astep, A]
    have hbd1 : St.Bd B { st with P := st.P + 1 } := by bdt
    refine read_b (l := .lb s) rfl hbd1 (getD_of_drop h1) ?_
    cases b <;>
    · refine step_of hbd1 ?_
      regs [astep, A, cond_true, cond_false]
      exact fin_of (by sext)
  | succ n ih =>
    intro st h hbd hx hV
    have h0 : x.drop st.P = true :: (List.replicate n true ++ false :: b :: rest) := by
      simpa [List.replicate_succ] using h
    have h1 := drop_succ_of_drop h0
    have hl := lt_of_drop h0
    refine read_t (l := .lc s) rfl hbd (getD_of_drop h0) ?_
    refine step_of hbd ?_
    regs [astep, A]
    have hbd1 : St.Bd B { st with V := st.V + 1 } := by bdt
    refine step_of hbd1 ?_
    regs [astep, A]
    have hbd2 : St.Bd B { st with V := st.V + 1, P := st.P + 1 } := by bdt
    have := ih { st with V := st.V + 1, P := st.P + 1 } h1 hbd2 hx (by simp; omega)
    refine reach_of_eq this ?_
    congr 3
    sext

/-- **The lookup of a literal**: from `lv false b` at depth `K`, with `T`, `Z`, `C` clear, the
machine reaches `cl s'` with `s'` whether the variable `V` reads `b` under `asg K S`, and
clears `V`.

**Proof sketch.** `C := K` (copy), `C := C - V` (`sb_run`). If `C = 0`, the variable is free
and reads `0`. Otherwise `C := C - 1`, `T := S` (copy), `T := T / 2 ^ C` (`hv_run`), and the
oddness of `T` is bit `K - 1 - V` of `S`; `T` is cleared. -/
theorem lv_run (b : Bool) (st : St) (hbd : st.Bd B) (hT : st.T = 0) (hZ : st.Z = 0)
    (hC : st.C = 0) :
    Run x B (.lv false b) st (.cl (asg st.K st.S st.V == b)) { st with V := 0 } := by
  have hb0 := hbd
  simp only [St.Bd] at hb0
  refine step_of hbd ?_
  regs [astep, A, Bool.false_eq_true, if_false]
  have e0 : { st with T := 0 } = st := by ext <;> simp [hT]
  rw [e0]
  refine (cp_run (.lK b) st hbd hZ (by simp only [cpDst, cpSrc]; regs; omega)).trans ?_
  regs [cpDst, cpSrc, cpExit]
  have hbd1 : St.Bd B { st with C := st.C + st.K } := by bdt
  refine (sb_run b _ hbd1).trans ?_
  have hbd2 : St.Bd B { st with V := 0, C := st.C + st.K - st.V } := by bdt
  refine step_of hbd2 ?_
  regs [astep, A]
  by_cases hk : st.C + st.K - st.V = 0
  · rw [if_pos hk]
    have ha : asg st.K st.S st.V = false := by
      simp [asg, show ¬ st.V < st.K by omega]
    rw [ha]
    cases b <;> exact fin_of (by sext)
  · rw [if_neg hk]
    refine step_of hbd2 ?_
    regs [astep, A]
    set st3 : St := { st with V := 0, C := st.C + st.K - st.V - 1 } with hst3
    have hbd3 : St.Bd B st3 := by simp only [hst3]; bdt
    refine (cp_run (.lS b) st3 hbd3 (by simp [hst3, hZ])
      (by simp only [cpDst, cpSrc]; regs; simp only [hst3]; omega)).trans ?_
    regs [cpDst, cpSrc, cpExit]
    have hbd4 : St.Bd B { st3 with T := st3.T + st3.S } := by simp only [hst3]; bdt
    refine (hv_run b _ hbd4).trans ?_
    set q := (st3.T + st3.S) / 2 ^ st3.C with hq
    have hqS : q ≤ st.S := by
      simp only [hq, hst3, hT, zero_add]; exact Nat.div_le_self _ _
    have hbd5 : St.Bd B { st3 with T := q, C := 0 } := by simp only [hst3]; bdt
    have ha : asg st.K st.S st.V = decide (q % 2 = 1) := by
      simp only [asg, hq, hst3, hT, hC, zero_add]
      rw [show st.K - st.V - 1 = st.K - 1 - st.V by omega]
      simp [show st.V < st.K by omega]
    refine step_of (st := { st3 with T := q, C := 0 }) hbd5 ?_
    regs [astep, A]
    by_cases ho : q % 2 = 1
    · rw [if_pos ho]
      refine step_of hbd5 ?_
      regs [astep, A]
      rw [ha, decide_eq_true ho]
      cases b <;> exact fin_of (by sext [hst3, hC])
    · rw [if_neg ho]
      refine step_of hbd5 ?_
      regs [astep, A]
      rw [ha, decide_eq_false ho]
      cases b <;> exact fin_of (by sext [hst3, hC])

/-- **A literal**: from `lt s` with the input at `P` reading the serialization of `(v, b)`,
and `T`, `Z`, `C`, `V` clear, the machine moves `P` past the literal and reaches `cl s'` with
`s'` whether the clause is satisfied so far (`s`, or `v` reads `b` under `asg K S`).

**Proof sketch.** Skip the first `1` of the unary run, count the rest (`lc_run`); if the
clause is already satisfied clear `V`, otherwise look the variable up (`lv_run`). -/
theorem lit_run (s : Bool) (v : ℕ) (b : Bool) (rest : List Bool) (st : St)
    (h : x.drop st.P = CNF.serializeLit (v, b) ++ rest) (hbd : st.Bd B) (hx : x.length ≤ B)
    (hT : st.T = 0) (hZ : st.Z = 0) (hC : st.C = 0) (hV : st.V = 0) :
    Run x B (.lt s) st (.cl (s || (asg st.K st.S v == b))) { st with P := st.P + v + 3 } := by
  have hl := le_of_drop h (by simp [CNF.serializeLit])
  simp only [CNF.serializeLit, List.length_append, List.length_replicate, List.length_cons,
    List.length_nil] at hl
  have h0 : x.drop st.P = true :: (List.replicate v true ++ false :: b :: rest) := by
    simpa [CNF.serializeLit, List.replicate_succ] using h
  refine step_of hbd ?_
  regs [astep, A]
  have hbd1 : St.Bd B { st with P := st.P + 1 } := by bdt
  refine (lc_run s b rest v _ (drop_succ_of_drop h0) hbd1 hx (by simp; omega)).trans ?_
  have hbd2 : St.Bd B { st with P := st.P + 1 + v + 2, V := st.V + v } := by bdt
  cases s
  · have := lv_run (x := x) b _ hbd2 hT hZ hC
    simp only [hV, zero_add] at this ⊢
    refine reach_of_eq this ?_
    simp only [Bool.false_or]
    congr 3
    sext
  · refine step_of hbd2 ?_
    regs [astep, A, if_true]
    exact fin_of (by sext [hV])

/-- **A clause**: from `cl s` with the input at `P` reading the literals of `Cl` and the
clause terminator, and `T`, `Z`, `C`, `V` clear, the machine reaches `ce s'` at the terminator,
`s'` being `s` or the value of `Cl` under `asg K S`.

**Proof sketch.** Induction on `Cl`: a `0` ends the clause; a `1` starts a literal
(`lit_run`). -/
theorem clause_run (rest : List Bool) : ∀ (Cl : CNF.Clause ℕ) (s : Bool) (st : St),
    x.drop st.P = Cl.flatMap CNF.serializeLit ++ false :: rest → st.Bd B → x.length ≤ B →
    st.T = 0 → st.Z = 0 → st.C = 0 → st.V = 0 →
    Run x B (.cl s) st (.ce (s || CNF.Clause.eval (asg st.K st.S) Cl))
      { st with P := st.P + (Cl.flatMap CNF.serializeLit).length } := by
  intro Cl
  induction Cl with
  | nil =>
    intro s st h hbd hx hT hZ hC hV
    simp only [List.flatMap_nil, List.nil_append] at h
    refine read_f (l := .cl s) rfl hbd (getD_of_drop h) ?_
    rw [CNF.Clause.eval_nil, Bool.or_false]
    exact fin_of (by sext)
  | cons ℓ Cl ih =>
    intro s st h hbd hx hT hZ hC hV
    obtain ⟨v, b⟩ := ℓ
    have h' : x.drop st.P = CNF.serializeLit (v, b) ++
        (Cl.flatMap CNF.serializeLit ++ false :: rest) := by
      simpa [List.append_assoc] using h
    have hh : x.drop st.P = true :: (List.replicate v true ++ [false, b] ++
        (Cl.flatMap CNF.serializeLit ++ false :: rest)) := by
      simpa [CNF.serializeLit, List.replicate_succ, List.append_assoc] using h'
    refine read_t (l := .cl s) rfl hbd (getD_of_drop hh) ?_
    refine (lit_run s v b _ st h' hbd hx hT hZ hC hV).trans ?_
    have h2 := drop_add_of_drop h'
    simp only [CNF.serializeLit, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil] at h2
    have hl := le_of_drop h' (by simp [CNF.serializeLit])
    simp only [CNF.serializeLit, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil] at hl
    have hbd1 : St.Bd B { st with P := st.P + v + 3 } := by bdt
    have := ih (s || (asg st.K st.S v == b)) { st with P := st.P + v + 3 }
      (by simpa [Nat.add_assoc] using h2) hbd1 hx hT hZ hC hV
    refine reach_of_eq this ?_
    simp only [CNF.Clause.eval_cons, Bool.or_assoc]
    congr 3
    sext [CNF.serializeLit]

/-- **The matrix**: from `fm` with the input at `P` reading the serialization of `φ`, and
`T`, `Z`, `C`, `V` clear, the machine reaches `rt v` with `v` the value of `φ` under
`asg K S`, and clears `P`.

**Proof sketch.** Induction on `φ`: a `0` ends the formula (value `1`); a `1` announces a
clause (`clause_run`), after whose terminator the machine continues if the clause is
satisfied and returns `0` otherwise. -/
theorem formula_run (rest : List Bool) : ∀ (φ : CNF ℕ) (st : St),
    x.drop st.P = CNF.serialize φ ++ rest → st.Bd B → x.length ≤ B →
    st.T = 0 → st.Z = 0 → st.C = 0 → st.V = 0 →
    Run x B .fm st (.rt (CNF.eval (asg st.K st.S) φ)) { st with P := 0 } := by
  intro φ
  induction φ with
  | nil =>
    intro st h hbd hx hT hZ hC hV
    simp only [CNF.serialize, List.flatMap_nil, List.nil_append, List.cons_append] at h
    refine read_f (l := .fm) rfl hbd (getD_of_drop h) ?_
    refine step_of hbd ?_
    regs [astep, A]
    exact fin_of rfl
  | cons Cl φ ih =>
    intro st h hbd hx hT hZ hC hV
    have h0 : x.drop st.P = true :: (Cl.flatMap CNF.serializeLit ++ false ::
        (CNF.serialize φ ++ rest)) := by
      simpa [CNF.serialize, CNF.serializeClause, List.append_assoc] using h
    have h1 := drop_succ_of_drop h0
    have hl := le_of_drop (u := Cl.flatMap CNF.serializeLit ++ [false])
      (by simpa [List.append_assoc] using h1) (by simp)
    simp only [List.length_append, List.length_cons, List.length_nil] at hl
    refine read_t (l := .fm) rfl hbd (getD_of_drop h0) ?_
    refine step_of hbd ?_
    regs [astep, A]
    have hbd1 : St.Bd B { st with P := st.P + 1 } := by bdt
    refine (clause_run _ Cl false _ h1 hbd1 hx hT hZ hC hV).trans ?_
    simp only [Bool.false_or]
    set P1 := st.P + 1 + (Cl.flatMap CNF.serializeLit).length with hP1
    have hbd2 : St.Bd B { st with P := P1 } := by bdt
    refine step_of hbd2 ?_
    regs [astep, A]
    have h2 : x.drop (P1 + 1) = CNF.serialize φ ++ rest := by
      have := drop_add_of_drop (u := Cl.flatMap CNF.serializeLit ++ [false]) (p := st.P + 1)
        (by simpa [List.append_assoc] using h1)
      simpa [hP1, Nat.add_assoc] using this
    have hbd3 : St.Bd B { st with P := P1 + 1 } := by bdt
    cases hc : CNF.Clause.eval (asg st.K st.S) Cl
    · simp only [Bool.false_eq_true, if_false, CNF.eval_cons, hc, Bool.false_and]
      refine step_of hbd3 ?_
      regs [astep, A]
      exact fin_of (by ext <;> simp)
    · simp only [if_true, CNF.eval_cons, hc, Bool.true_and]
      have := ih { st with P := P1 + 1 } h2 hbd3 hx hT hZ hC hV
      refine reach_of_eq this ?_
      congr 3

end TQBFARM

end Complexity.LogProg
