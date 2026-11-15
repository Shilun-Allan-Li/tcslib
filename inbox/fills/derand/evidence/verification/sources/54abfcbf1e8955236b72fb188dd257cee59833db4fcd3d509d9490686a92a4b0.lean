/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.Lib
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implicitly logspace computable functions are computable in logspace and in polynomial time

[AB09, Def 4.16 and p. 112]: an implicitly logspace computable function can be computed by a
machine with a write-once output tape in logarithmic space — for `i = 0, 1, 2, …` ask the
length language whether `i` is a position of `f(x)` and, if so, ask the bit language for
`f(x)ᵢ` and write it — and logspace computations run in polynomial time, so the function is
polynomial-time computable.

The enumeration is a register-tape program (`Complexity.LogProg.RProg`) with one register,
the binary counter `i`, calling the two deciders on the virtual input `⟨x, i⟩`; it is
compiled with `Complexity.LogProg.compile_space` against the decider bank
`Complexity.LogProg.bankTM`.

## Main results

* `Complexity.ImplicitlyLogspaceComputable.computesInSpace` — some machine computes `f` in
  space `O(log n)`. [AB09, Def 4.16; Exercise 4.8, one direction]
* `Complexity.ImplicitlyLogspaceComputable.polyTimeComputable` — `f` is polynomial-time
  computable. [AB09, p. 112: "logspace computations run in polynomial time"]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Definition 4.16; §6.2.1, p. 112.)
-/

namespace Complexity

open Turing LogProg

/-- Membership of a pair in an index language. -/
lemma pairEncode_mem_indexLang (p : List Bool → ℕ → Prop) (x : List Bool) (i : ℕ) :
    pairEncode x (Nat.bits i) ∈ indexLang p ↔ p x i := by
  constructor
  · rintro ⟨x', i', h, hp⟩
    have := pairEncode_injective (a₁ := (x, Nat.bits i)) (a₂ := (x', Nat.bits i')) h
    simp only [Prod.mk.injEq] at this
    obtain ⟨rfl, hb⟩ := this
    rw [bits_injective hb]; exact hp
  · intro h; exact ⟨x, i, rfl, h⟩

namespace ImplicitEnum

/-- The states of the enumeration program. -/
inductive St where
  | ask | bit | emitT | emitF | incC | incB | done
  deriving DecidableEq, Fintype

/-- The ordinary transitions: emit a bit, increment the counter, halt. -/
def tm : MultiTapeTM 1 Bool St where
  q₀ := .ask
  tr
    | .emitT, _, _ => ⟨0, fun _ => (none, 0), some true, some .incC⟩
    | .emitF, _, _ => ⟨0, fun _ => (none, 0), some false, some .incC⟩
    | .incC, _, w => incCAct 0 .incC .incB (w 0)
    | .incB, _, w => incBAct 0 .incB .ask (w 0)
    | _, _, _ => ⟨0, fun _ => (none, 0), none, none⟩

/-- **The enumeration program**: at `ask`, ask decider `0` (the length language) about
`⟨x, i⟩`; at `bit`, ask decider `1` (the bit language); emit the answer; increment `i`. -/
def prog : RProg 1 2 St where
  tm := tm
  call
    | .ask => some ⟨0, .whole, [0], .bit, .done⟩
    | .bit => some ⟨1, .whole, [0], .emitT, .emitF⟩
    | _ => none

/-- The program configuration at the start of round `i`, having written `out`. -/
def cfg (x out : List Bool) (s : St) (i : ℕ) : Cfg 1 Bool St x :=
  ⟨some s, 1, fun _ => FinTM.bufferTape (Nat.bits i), fun _ => 0, out⟩

/-- The virtual input of both calls in round `i` is `⟨x, i⟩`. -/
lemma vword_call (x out : List Bool) (s : St) (i : ℕ) (dec : Fin 2) (yes no : St) :
    vword (callSegs ⟨dec, .whole, [0], yes, no⟩ x (regWords (cfg x out s i))) =
      pairEncode x (Nat.bits i) := by
  simp [callSegs, argSegs, regWords, cfg, tapeWord_bufferTape, vword, Mode.seg0, render,
    pairEncode_eq_dbl]

/-- The enumerator configuration `cfg x out s i` is in state `s`. -/
@[simp] lemma cfg_state (x out : List Bool) (s : St) (i : ℕ) : (cfg x out s i).state = some s :=
  rfl

/-- The call at `ask`. -/
lemma rstep_ask (o : Fin 2 → List Bool → Bool) (x out : List Bool) (i : ℕ) :
    rstep prog o (cfg x out .ask i) =
      cfg x out (if o 0 (pairEncode x (Nat.bits i)) then .bit else .done) i := by
  have h := vword_call x out .ask i 0 .bit .done
  have hc : prog.call .ask = some ⟨0, .whole, [0], .bit, .done⟩ := rfl
  simp only [rstep, cfg_state, hc]
  rw [h]; rfl

/-- The call at `bit`. -/
lemma rstep_bit (o : Fin 2 → List Bool → Bool) (x out : List Bool) (i : ℕ) :
    rstep prog o (cfg x out .bit i) =
      cfg x out (if o 1 (pairEncode x (Nat.bits i)) then .emitT else .emitF) i := by
  have h := vword_call x out .bit i 1 .emitT .emitF
  have hc : prog.call .bit = some ⟨1, .whole, [0], .emitT, .emitF⟩ := rfl
  simp only [rstep, cfg_state, hc]
  rw [h]; rfl

section Run

variable (f : List Bool → List Bool) (o : Fin 2 → List Bool → Bool)
  (ho0 : ∀ x i, o 0 (pairEncode x (Nat.bits i)) = decide (i < (f x).length))
  (ho1 : ∀ x i, o 1 (pairEncode x (Nat.bits i)) = (f x).getD i false)

/-- The configurations met along the run: a call configuration of some round, or an ordinary
configuration with the counter head in `[-1, W]`. -/
def Shape (x : List Bool) (F W : ℕ) (c : Cfg 1 Bool St x) : Prop :=
  (∃ out s i, i ≤ F ∧ (s = .ask ∨ s = .bit) ∧ c = cfg x out s i) ∨
  ((∀ l, c.state = some l → prog.call l = none) ∧ -1 ≤ c.workTapePos 0 ∧
    c.workTapePos 0 ≤ W)

/-- Writing the binary word of `n` on the counter of an enumerator configuration gives the
enumerator configuration with counter `n`. -/
lemma regCfg_cfg (x out : List Bool) (s s' : St) (i : ℕ) (n : ℕ) :
    regCfg (cfg x out s i) s' 0 (FinTM.bufferTape (Nat.bits n)) 0 = cfg x out s' n := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, cfg]
  · funext r; rw [Fin.fin_one_eq_zero r]; simp [regCfg, cfg]

include ho0 ho1 in
/-- **One round**: from round `i < |f x|` with `f(x)₀ … f(x)ᵢ₋₁` written, the program
writes `f(x)ᵢ` and reaches round `i + 1`.

**Proof sketch.** The round asks the bit decider (a call on `⟨x, bits i⟩`), emits the answer
`f(x)ᵢ` (`rstep_bit`), then increments the counter `i` with the increment fragment (`inc_run`).
Every intermediate configuration has the counter in binary of length at most `W` and output a
prefix of `f x`, which is `Shape`. -/
lemma round (x : List Bool) (i : ℕ) (hi : i < (f x).length) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : (Nat.bits (i + 1)).length ≤ W) :
    ∃ T, rrun prog o (cfg x ((f x).take i) .ask i) T = cfg x ((f x).take (i + 1)) .ask (i + 1) ∧
      ∀ t < T, Shape x F W (rrun prog o (cfg x ((f x).take i) .ask i) t) := by
  set b := (f x)[i] with hb
  have h1 : rrun prog o (cfg x ((f x).take i) .ask i) 1 = cfg x ((f x).take i) .bit i := by
    rw [rrun_one, rstep_ask, ho0]
    simp [hi]
  have h2 : rrun prog o (cfg x ((f x).take i) .bit i) 1 =
      cfg x ((f x).take i) (if b then .emitT else .emitF) i := by
    rw [rrun_one, rstep_bit, ho1]
    simp [hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have h3 : rrun prog o (cfg x ((f x).take i) (if b then .emitT else .emitF) i) 1 =
      cfg x ((f x).take (i + 1)) .incC i := by
    rw [rrun_one, rstep_noncall prog o _ (if b then .emitT else .emitF) rfl (by cases b <;> rfl)]
    unfold MultiTapeTM.step
    simp only [cfg]
    have ht : (f x).take (i + 1) = (f x).take i ++ [b] := by
      rw [hb, List.take_succ, List.getElem?_eq_getElem hi]; rfl
    rw [ht]
    cases b <;> (refine Cfg.ext rfl ?_ ?_ ?_ ?_) <;> simp [prog, tm, Action.apply]
  obtain ⟨T₄, h4, hm4⟩ := inc_run prog o 0 .incC .incB .ask (fun _ _ => rfl) (fun _ _ => rfl)
    rfl rfl (cfg x ((f x).take (i + 1)) .incC i) i
  rw [regCfg_cfg, regCfg_cfg] at h4
  refine ⟨1 + (1 + (1 + T₄)), ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, rrun_add, h2, rrun_add, h3, h4]
  · rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl ⟨_, .ask, i, by omega, Or.inl rfl, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h1]
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      exact Or.inl ⟨_, .bit, i, by omega, Or.inr rfl, rfl⟩
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h2]
    rcases Nat.lt_or_ge t 1 with h | h
    · obtain rfl : t = 0 := by omega
      refine Or.inr ⟨fun l hl => ?_, by simp [rrun_zero, cfg], by simp [rrun_zero, cfg]⟩
      simp only [rrun_zero, cfg, Option.some.injEq] at hl
      subst hl; cases b <;> rfl
    obtain ⟨t, rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
    rw [rrun_add, h3]
    obtain ⟨s', f', q, hq, hs', hq1, hq2⟩ := hm4 t (by omega)
    rw [regCfg_cfg] at hq
    rw [hq]
    refine Or.inr ⟨fun l hl => ?_, ?_, ?_⟩
    · simp only [regCfg, Option.some.injEq] at hl
      subst hl; rcases hs' with rfl | rfl <;> rfl
    · simpa [regCfg] using hq1
    · simp only [regCfg, Function.update_self]; omega

include ho0 ho1 in
/-- All rounds: from the start the program reaches round `i ≤ |f x|`. -/
lemma rounds (x : List Bool) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : ∀ i < (f x).length, (Nat.bits (i + 1)).length ≤ W) :
    ∀ i ≤ (f x).length, ∃ T, rrun prog o (cfg x [] .ask 0) T = cfg x ((f x).take i) .ask i ∧
      ∀ t < T, Shape x F W (rrun prog o (cfg x [] .ask 0) t) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨0, by simp [rrun_zero], fun t ht => absurd ht (by omega)⟩
  | succ i ih =>
    intro hi
    obtain ⟨T₁, h1, hm1⟩ := ih (by omega)
    obtain ⟨T₂, h2, hm2⟩ := round f o ho0 ho1 x i (by omega) F W hF (hW i (by omega))
    refine ⟨T₁ + T₂, by rw [rrun_add, h1, h2], fun t ht => ?_⟩
    rcases Nat.lt_or_ge t T₁ with h | h
    · exact hm1 t h
    · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
      rw [rrun_add, h1]; exact hm2 t' (by omega)

include ho0 ho1 in
/-- **The whole run**: the program halts with output `f x`, every configuration before the
halt having the shape `Shape`.

**Proof sketch.** Induction on the number of rounds: `round` takes round `i` to round `i + 1`
for `i < |f x|`; at `i = |f x|` the length decider answers no and the program halts with output
`f x` and counter head home. The shape invariant is collected round by round. -/
lemma run (x : List Bool) (F W : ℕ) (hF : (f x).length ≤ F)
    (hW : ∀ i < (f x).length, (Nat.bits (i + 1)).length ≤ W) :
    ∃ N, (rrun prog o (Cfg.init .ask x) N).state = none ∧
      (rrun prog o (Cfg.init .ask x) N).output = f x ∧
      (rrun prog o (Cfg.init .ask x) N).workTapePos 0 = 0 ∧
      ∀ t < N, Shape x F W (rrun prog o (Cfg.init .ask x) t) := by
  have hinit : (Cfg.init .ask x : Cfg 1 Bool St x) = cfg x [] .ask 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext r z; simp [cfg, Nat.zero_bits]
  rw [hinit]
  obtain ⟨T, h1, hm1⟩ := rounds f o ho0 ho1 x F W hF hW (f x).length le_rfl
  rw [List.take_length] at h1
  have h2 : rrun prog o (cfg x (f x) .ask (f x).length) 1 = cfg x (f x) .done (f x).length := by
    rw [rrun_one, rstep_ask, ho0]; simp
  have h3 : (rrun prog o (cfg x (f x) .done (f x).length) 1).state = none ∧
      (rrun prog o (cfg x (f x) .done (f x).length) 1).output = f x ∧
      (rrun prog o (cfg x (f x) .done (f x).length) 1).workTapePos 0 = 0 := by
    rw [rrun_one, rstep_noncall prog o _ .done rfl rfl]
    simp [MultiTapeTM.step, cfg, prog, tm, Action.apply]
  refine ⟨T + (1 + 1), ?_, ?_, ?_, fun t ht => ?_⟩
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.1
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.2.1
  · rw [rrun_add, h1, rrun_add, h2]; exact h3.2.2
  · rcases Nat.lt_or_ge t T with h | h
    · exact hm1 t h
    · obtain ⟨t', rfl⟩ : ∃ t', t = T + t' := ⟨t - T, by omega⟩
      rw [rrun_add, h1]
      rcases Nat.lt_or_ge t' 1 with h' | h'
      · obtain rfl : t' = 0 := by omega
        exact Or.inl ⟨_, .ask, _, hF, Or.inl rfl, rfl⟩
      · obtain rfl : t' = 1 := by omega
        rw [h2]
        refine Or.inr ⟨fun l hl => ?_, by simp [cfg], by simp [cfg]⟩
        simp only [cfg_state, Option.some.injEq] at hl
        subst hl; rfl

end Run

end ImplicitEnum

/-- **Implicitly logspace computable functions are computable in logspace** [AB09, Def 4.16;
one direction of Exercise 4.8]: some machine computes `f` visiting `O(log n)` work cells.

**Proof sketch.** The enumeration program `ImplicitEnum.prog` keeps `i` in binary on one
register and, for `i = 0, 1, …`, asks the length language and the bit language about `⟨x, i⟩`
and writes the answer (`ImplicitEnum.run`). `i ≤ |f(x)| ≤ C (n+1)^e`, so the counter has
`O(log n)` bits, and the deciders run on inputs of length `2n + 2 + O(log n)`, in space
`O(log n)`. `compile_space` turns the program into a machine computing `f` within the
register range plus `kD (2B + 1)` cells, which `log_poly_bound` shows to be `O(log n)`. -/
theorem ImplicitlyLogspaceComputable.computesInSpace {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesInSpace f fun n => c * logSpace n := by
  classical
  obtain ⟨⟨C, e, hlen⟩, ⟨c1, M1, hM1⟩, ⟨c0, M0, hM0⟩⟩ := hf
  let Ms : Fin 2 → FinTM Bool := fun j => if j = 0 then M0 else M1
  let A : Fin 2 → Language Bool := fun j => if j = 0 then
    indexLang (fun x i => i < (f x).length) else indexLang (fun x i => (f x).getD i false = true)
  let s : Fin 2 → ℕ → ℕ := fun j n => if j = 0 then c0 * logSpace n else c1 * logSpace n
  have hMs : ∀ j, (Ms j).DecidesInSpace (A j) (s j) := by
    intro j
    by_cases hj : j = 0
    · subst hj; simpa [Ms, A, s] using hM0
    · have hj1 : j = 1 := Fin.ext (by
        have := j.isLt; have : j.val ≠ 0 := fun h => hj (Fin.ext h); simp; omega)
      subst hj1; simpa [Ms, A, s] using hM1
  let o : Fin 2 → List Bool → Bool := fun j V => MultiTapeTM.indicator (A j : Set (List Bool)) V
  have ho0 : ∀ x i, o 0 (pairEncode x (Nat.bits i)) = decide (i < (f x).length) := by
    intro x i
    have := pairEncode_mem_indexLang (fun x i => i < (f x).length) x i
    by_cases h : i < (f x).length <;>
      simp_all [o, A, MultiTapeTM.indicator]
  have ho1 : ∀ x i, o 1 (pairEncode x (Nat.bits i)) = (f x).getD i false := by
    intro x i
    have := pairEncode_mem_indexLang (fun x i => (f x).getD i false = true) x i
    cases h : (f x).getD i false <;> simp_all [o, A, MultiTapeTM.indicator]
  obtain ⟨K1, hK1⟩ := LogProg.log_poly_bound C e 1
  obtain ⟨K2, hK2⟩ := LogProg.log_poly_bound (C + 2) (e + 1) 2
  set kD := bankK Ms + bankK Ms with hkD
  refine ⟨compileFinTM ImplicitEnum.prog .ask (bankTM Ms) (bankStart Ms),
    K1 + 2 + kD * (2 * ((c0 + c1) * K2 + 1) + 1), fun x => ?_⟩
  set n := x.length with hn
  set F := C * (n + 1) ^ e with hFdef
  set W := Nat.log 2 (F + 1) + 1 with hWdef
  set B := (c0 + c1) * logSpace (2 * n + 2 + W) + 1 with hBdef
  have hF : (f x).length ≤ F := hlen x
  have hbitsW : ∀ i ≤ F + 1, (Nat.bits i).length ≤ W := fun i hi =>
    (LogProg.length_bits_le_log i).trans (by have := Nat.log_mono_right (b := 2) hi; omega)
  obtain ⟨N, hN1, hN2, hN3, hNs⟩ := ImplicitEnum.run f o ho0 ho1 x F W hF
    (fun i hi => hbitsW (i + 1) (by omega))
  have hbox : ∀ t ≤ N, ∀ r : Fin 1, (-1 : ℤ) ≤ (rrun ImplicitEnum.prog o (Cfg.init .ask x) t).workTapePos r ∧
      (rrun ImplicitEnum.prog o (Cfg.init .ask x) t).workTapePos r ≤ (W : ℤ) := by
    intro t ht r
    rw [Fin.fin_one_eq_zero r]
    rcases Nat.lt_or_ge t N with h | h
    · rcases hNs t h with ⟨out, s', i, -, -, hc⟩ | ⟨-, h1, h2⟩
      · rw [hc]; simp [ImplicitEnum.cfg]
      · exact ⟨h1, h2⟩
    · obtain rfl : t = N := by omega
      rw [hN3]; simp
  have hcalls : ∀ t < N, CallOK ImplicitEnum.prog (bankTM Ms) (bankStart Ms) o (fun _ => -1)
      (fun _ => (W : ℤ)) B (rrun ImplicitEnum.prog o (Cfg.init .ask x) t) := by
    intro t ht l cs hl hcs
    rcases hNs t ht with ⟨out, s', i, hi, hs', hc⟩ | ⟨hnc, -, -⟩
    · rw [hc] at hl ⊢
      simp only [ImplicitEnum.cfg_state, Option.some.injEq] at hl
      subst hl
      have hreg : regWords (ImplicitEnum.cfg x out s' i) = fun _ => Nat.bits i := by
        funext r; simp [regWords, ImplicitEnum.cfg, tapeWord_bufferTape]
      have hV : vword (callSegs cs x (regWords (ImplicitEnum.cfg x out s' i))) =
          pairEncode x (Nat.bits i) := by
        rcases hs' with rfl | rfl <;> simp only [ImplicitEnum.prog, Option.some.injEq] at hcs <;>
          (subst hcs; exact ImplicitEnum.vword_call _ _ _ _ _ _ _)
      have hargs : cs.args = [0] := by
        rcases hs' with rfl | rfl <;> simp only [ImplicitEnum.prog, Option.some.injEq] at hcs <;>
          (subst hcs; rfl)
      refine ⟨by rw [hargs]; simp, rfl, ?_, ?_⟩
      · intro r hr
        rw [hargs] at hr
        simp only [List.mem_singleton] at hr
        subst hr
        rw [hreg]
        refine ⟨rfl, rfl, le_rfl, ?_⟩
        beta_reduce
        exact_mod_cast hbitsW i (by omega)
      · rw [hV]
        refine (bank_cleanRun Ms A s hMs cs.dec _).mono ?_
        have hlenV : (pairEncode x (Nat.bits i)).length ≤ 2 * n + 2 + W := by
          have := hbitsW i (by omega)
          simp [pairEncode, hn]; omega
        have hsj : s cs.dec (pairEncode x (Nat.bits i)).length ≤
            (c0 + c1) * logSpace (2 * n + 2 + W) := by
          have hm := logSpace_mono hlenV
          simp only [s]
          split_ifs
          · exact (Nat.mul_le_mul_left c0 hm).trans (Nat.mul_le_mul_right _ (by omega))
          · exact (Nat.mul_le_mul_left c1 hm).trans (Nat.mul_le_mul_right _ (by omega))
        simp only [hBdef]
        omega
    · exact absurd hcs (by rw [hnc l hl]; simp)
  obtain ⟨T, hT, hTs⟩ := compile_space ImplicitEnum.prog .ask (bankTM Ms) (bankStart Ms) o
    (fun _ => -1) (fun _ => (W : ℤ)) B N (f x) hN1 hN2 hbox hcalls
  refine ⟨T, hT, hTs.trans ?_⟩
  -- the arithmetic
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  have hW2 : (((W : ℤ) - -1 + 1).toNat) = W + 2 := by omega
  rw [hW2]
  set L := logSpace n with hL
  have hL1 : 1 ≤ L := by simp [hL, logSpace]
  have hWL : W + 2 ≤ (K1 + 2) * L := by
    have := hK1 n
    simp only [hWdef, hFdef]
    have : (K1 + 2) * L = K1 * L + 2 * L := by ring
    simp only [logSpace] at hL
    rw [hL] at *
    omega
  have hlogW : logSpace (2 * n + 2 + W) ≤ K2 * L := by
    have hWle : W ≤ F + 2 := by
      have := Nat.log_le_self 2 (F + 1); omega
    have hle : 2 * n + 2 + W ≤ (C + 2) * (n + 1) ^ (e + 1) + 2 := by
      have h1 : n + 1 ≤ (n + 1) ^ (e + 1) := by
        calc n + 1 = (n + 1) ^ 1 := by ring
          _ ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : (n + 1) ^ e ≤ (n + 1) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : F ≤ C * (n + 1) ^ (e + 1) := Nat.mul_le_mul_left C h2
      have : (C + 2) * (n + 1) ^ (e + 1) = C * (n + 1) ^ (e + 1) + 2 * (n + 1) ^ (e + 1) := by
        ring
      omega
    have := hK2 n
    have hm := logSpace_mono hle
    simp only [logSpace] at hm this ⊢
    simp only [hL, logSpace]
    omega
  have hBL : 2 * B + 1 ≤ (2 * ((c0 + c1) * K2 + 1) + 1) * L := by
    have h1 : (c0 + c1) * logSpace (2 * n + 2 + W) ≤ (c0 + c1) * (K2 * L) :=
      Nat.mul_le_mul_left _ hlogW
    have e1 : (2 * ((c0 + c1) * K2 + 1) + 1) * L = 2 * ((c0 + c1) * (K2 * L)) + 3 * L := by ring
    rw [e1]
    simp only [hBdef]
    omega
  calc W + 2 + kD * (2 * B + 1) ≤ (K1 + 2) * L + kD * ((2 * ((c0 + c1) * K2 + 1) + 1) * L) :=
        Nat.add_le_add hWL (Nat.mul_le_mul_left _ hBL)
    _ = (K1 + 2 + kD * (2 * ((c0 + c1) * K2 + 1) + 1)) * L := by ring

/-- **Implicitly logspace computable functions are polynomial-time computable**
[AB09, p. 112: "logspace computations run in polynomial time"].

**Proof sketch.** `ImplicitlyLogspaceComputable.computesInSpace` gives a machine computing
`f` in logarithmic space; by configuration counting
(`Complexity.polyTimeComputable_of_computesInSpace`) it runs in polynomial time. -/
theorem ImplicitlyLogspaceComputable.polyTimeComputable {f : List Bool → List Bool}
    (hf : ImplicitlyLogspaceComputable f) : PolyTimeComputable f := by
  obtain ⟨M, c, hM⟩ := hf.computesInSpace
  exact polyTimeComputable_of_computesInSpace hM

end Complexity
