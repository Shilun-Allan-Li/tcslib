/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun
import TCSlib.Complexity.SpaceComplexity.Machines.Bank
import TCSlib.Complexity.SpaceComplexity.ConfigCount

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proving abstract register machines correct

Reasoning about abstract register machines (`Complexity.LogProg.ARM`) happens on values: runs
`Complexity.LogProg.AReach` between abstract configurations through configurations satisfying
an invariant, composed sequentially. `Complexity.LogProg.arm_decides` turns a correct
abstract machine — one answering membership in a language on every input, with values of
logarithmically many binary digits — into a logspace decider.

## Main definitions

* `Complexity.LogProg.AReach`, `Complexity.LogProg.AHalt` — runs of abstract machines.

## Main results

* `Complexity.LogProg.arm_decides` — a correct abstract machine with logarithmic register
  values, calling logspace deciders on short virtual inputs, decides its language in `L`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- A run of an abstract machine from `a` to `a'` through configurations satisfying `G`. -/
def AReach (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a a' : AConf m Λ) : Prop :=
  ∃ T, arun A oracle x a T = a' ∧ ∀ t < T, G (arun A oracle x a t)

/-- A run of an abstract machine from `a` answering `b`, through configurations satisfying `G`. -/
def AHalt (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a : AConf m Λ) (b : Bool) : Prop :=
  ∃ T, (arun A oracle x a T).1 = none ∧ (arun A oracle x a T).2.2 = some b ∧
    ∀ t < T, G (arun A oracle x a t)

section Combinators

variable {A : ARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- Running `s + t` steps is running `s` steps, then `t` steps. -/
lemma arun_add (a : AConf m Λ) (s t : ℕ) :
    arun A oracle x a (s + t) = arun A oracle x (arun A oracle x a s) t := by
  simp only [arun]; rw [Nat.add_comm, Function.iterate_add_apply]

/-- Every configuration reaches itself (in zero steps). -/
lemma AReach.refl (a : AConf m Λ) : AReach A oracle x G a a := ⟨0, rfl, fun t h => by omega⟩

/-- Runs compose: a run from `a` to `b` followed by one from `b` to `c` is a run from `a` to `c`. -/
lemma AReach.trans {a b c : AConf m Λ} (h₁ : AReach A oracle x G a b)
    (h₂ : AReach A oracle x G b c) : AReach A oracle x G a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [arun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [arun_add, e1]; exact m2 t' (by omega)

/-- A run from `a` to `b` followed by a halting run from `b` is a halting run from `a`, with
the same answer. -/
lemma AReach.halt {a b : AConf m Λ} {r : Bool} (h₁ : AReach A oracle x G a b)
    (h₂ : AHalt A oracle x G b r) : AHalt A oracle x G a r := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [arun_add, e1]; exact f1, by rw [arun_add, e1]; exact f2, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [arun_add, e1]; exact m2 t' (by omega)

/-- A configuration satisfying the guard reaches its successor in one step. -/
lemma AReach.single {a : AConf m Λ} (hG : G a) :
    AReach A oracle x G a (astep A oracle x a) := ⟨1, rfl, fun t ht => by
  obtain rfl : t = 0 := by omega
  exact hG⟩

/-- A step followed by a run. -/
lemma AReach.step {a c : AConf m Λ} (hG : G a) (h : AReach A oracle x G (astep A oracle x a) c) :
    AReach A oracle x G a c := (AReach.single hG).trans h

/-- A step followed by a halting run. -/
lemma AHalt.step {a : AConf m Λ} {r : Bool} (hG : G a)
    (h : AHalt A oracle x G (astep A oracle x a) r) : AHalt A oracle x G a r :=
  (AReach.single hG).halt h

/-- Answering in one step. -/
lemma AHalt.ret {l : Λ} {v : Fin m → ℕ} {r : Bool} (hA : A l = .ret r)
    (hG : G (some l, v, none)) : AHalt A oracle x G (some l, v, none) r :=
  ⟨1, by simp [arun, astep, hA], by simp [arun, astep, hA], fun t ht => by
    obtain rfl : t = 0 := by omega
    exact hG⟩

/-- A run through configurations satisfying `G` also runs through configurations satisfying any
weaker `G'`. -/
lemma AReach.mono {G' : AConf m Λ → Prop} {a b : AConf m Λ} (h : AReach A oracle x G a b)
    (hG : ∀ c, G c → G' c) : AReach A oracle x G' a b := by
  obtain ⟨T, e, hm⟩ := h; exact ⟨T, e, fun t ht => hG _ (hm t ht)⟩

/-- A halting run through configurations satisfying `G` also runs through configurations
satisfying any weaker `G'`. -/
lemma AHalt.mono {G' : AConf m Λ → Prop} {a : AConf m Λ} {r : Bool} (h : AHalt A oracle x G a r)
    (hG : ∀ c, G c → G' c) : AHalt A oracle x G' a r := by
  obtain ⟨T, e1, e2, hm⟩ := h; exact ⟨T, e1, e2, fun t ht => hG _ (hm t ht)⟩

end Combinators

/-! ## From abstract machines to `L` -/

/-- A clean run within a head range is a clean run within any larger range. -/
lemma cleanRun_mono {kD : ℕ} {SD : Type} {D : MultiTapeTM kD Bool SD} {q : SD}
    {V : List Bool} {b : Bool} {B B' : ℕ} (h : CleanRun D q V b B) (hB : B ≤ B') :
    CleanRun D q V b B' := by
  obtain ⟨T, h1, h2, h3, h4, h5⟩ := h
  exact ⟨T, h1, h2, h3, h4, fun t ht i => (h5 t ht i).trans (by exact_mod_cast hB)⟩

/-- The syntactic preconditions of an abstract step (the decider part of `Pre` is discharged
by `arm_decides`). -/
def PreS (A : ARM m d Λ) (x : List Bool) : AConf m Λ → Prop
  | (some l, _, _) =>
    match A l with
    | .jeq r s _ _ => r ≠ s
    | .jeqIn _ _ _ => ValidPlain x
    | .jeqFst _ _ _ => ValidPair x
    | .jeqSnd _ _ _ => ValidPair x
    | .call _ _ args _ _ => args.Nodup
    | _ => True
  | _ => True

/-- A virtual input is at most as long as its segments' renderings plus two separator symbols
per segment. -/
lemma length_vword_le (segs : List Seg) :
    (vword segs).length ≤ (segs.map rlen).sum + 2 * segs.length := by
  induction segs with
  | nil => simp [vword]
  | cons s rest ih =>
    cases rest with
    | nil => simp [vword]
    | cons t rest' =>
      simp only [vword, List.length_append, length_render, List.length_cons, List.length_nil,
        List.map_cons, List.sum_cons] at ih ⊢
      omega

/-- Every register segment of a call comes from one of the argument words. -/
lemma mem_argSegs {ws : List (List Bool)} {sg : Seg} (h : sg ∈ argSegs ws) : sg.1 ∈ ws := by
  induction ws with
  | nil => simp [argSegs] at h
  | cons w ws ih =>
    cases ws with
    | nil => simp [argSegs] at h; simp [h]
    | cons v ws' =>
      simp only [argSegs, List.mem_cons] at h
      rcases h with rfl | h
      · simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- The renderings of the register segments of argument words of length at most `W` have total
length at most `2W` per word. -/
lemma sum_rlen_argSegs_le (ws : List (List Bool)) (W : ℕ) (h : ∀ w ∈ ws, w.length ≤ W) :
    ((argSegs ws).map rlen).sum ≤ ws.length * (2 * W) := by
  have hle : ∀ y ∈ (argSegs ws).map rlen, y ≤ 2 * W := by
    intro y hy
    obtain ⟨sg, hs, rfl⟩ := List.mem_map.mp hy
    have := h _ (mem_argSegs hs)
    obtain ⟨w', bb⟩ := sg
    cases bb <;> simp [rlen] at this ⊢ <;> omega
  have := List.sum_le_card_nsmul _ _ hle
  simpa using this

/-- The virtual input of a call is short when the registers are.

**Proof sketch.** The virtual input is the leading segment (the input doubled, or its leading
run of `1`s, of rendered length at most `2|x|`) and one segment per argument register. There are
at most `m` arguments since they are distinct (`hnd`), each rendered with length at most `2W`,
plus two separator symbols per segment (`length_vword_le`, `sum_rlen_argSegs_le`). -/
lemma length_callSegs_le (cs : CallSpec m d Λ) (W : ℕ) (V : Fin m → List Bool)
    (hV : ∀ r, (V r).length ≤ W) (hnd : cs.args.Nodup) :
    (vword (callSegs cs x V)).length ≤ 2 * x.length + 2 + m * (2 * W + 2) := by
  have h1 := length_vword_le (callSegs cs x V)
  have hlen : cs.args.length ≤ m := by simpa using hnd.length_le_card
  have h0 : rlen (cs.mode.seg0 x) ≤ 2 * x.length := by
    cases cs.mode
    · simp [Mode.seg0, rlen]
    · simp only [Mode.seg0, rlen, Bool.false_eq_true, ↓reduceIte]
      have := (List.takeWhile_prefix (fun b => decide (b = true)) (l := x)).length_le; omega
  have h2 := sum_rlen_argSegs_le (cs.args.map V) W (by simp; intro r _; exact hV r)
  simp only [callSegs, List.map_cons, List.sum_cons, List.length_cons, length_argSegs,
    List.length_map] at h1 h2 ⊢
  have h3 : cs.args.length * (2 * W) ≤ m * (2 * W) := Nat.mul_le_mul_right _ hlen
  have h4 : m * (2 * W + 2) = m * (2 * W) + 2 * m := by ring
  rw [h4]
  generalize m * (2 * W) = P at h3 ⊢
  generalize cs.args.length * (2 * W) = Q at h2 h3
  omega

/-- **Abstract register machines with logarithmic registers decide languages in `L`**: if, on
every input `x`, the abstract machine `A` (calling deciders for languages in `L`) answers
`x ∈ L`, through configurations meeting the syntactic preconditions with every register value
of at most `K · logSpace |x|` binary digits (counting one increment), then `L ∈ L`.

**Proof sketch.** The deciders are collected in a clean bank (`bank_cleanRun`). Virtual inputs
of calls have length at most `2|x| + 2 + m (2W + 2)` (`length_callSegs_le`), linear in `|x|`,
so the deciders' head ranges are `O(log |x|)` (`log_poly_bound`). `arm_space` then gives a
machine answering `x ∈ L` within `m (W + 2) + kD (2B + 1) = O(log |x|)` cells. -/
theorem arm_decides {L : Language Bool} [Fintype Λ] [DecidableEq Λ] (A : ARM m d Λ) (l₀ : Λ)
    (As : Fin d → Language Bool) (hAs : ∀ j, As j ∈ LOGSPACE) (K : ℕ)
    (hcorr : ∀ x, AHalt A (fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V) x
      (fun a => PreS A x a ∧ ∀ r, (Nat.bits (a.2.1 r + 1)).length ≤ K * logSpace x.length)
      (some l₀, fun _ => 0, none) (MultiTapeTM.indicator (L : Set (List Bool)) x)) :
    L ∈ LOGSPACE := by
  classical
  have hc : ∀ j, ∃ (c : ℕ) (M : FinTM Bool), M.DecidesInSpace (As j) fun n => c * logSpace n :=
    fun j => hAs j
  let c : Fin d → ℕ := fun j => Classical.choose (hc j)
  let Ms : Fin d → FinTM Bool := fun j => Classical.choose (Classical.choose_spec (hc j))
  have hMs : ∀ j, (Ms j).DecidesInSpace (As j) fun n => c j * logSpace n :=
    fun j => Classical.choose_spec (Classical.choose_spec (hc j))
  set cs := ∑ j, c j with hcs
  have hcj : ∀ j, c j ≤ cs := fun j =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  set Q := 4 + 2 * m + 2 * m * K with hQ
  obtain ⟨K2, hK2⟩ := log_poly_bound Q 1 0
  set kD := bankK Ms + bankK Ms with hkD
  set oracle : Fin d → List Bool → Bool :=
    fun j V => MultiTapeTM.indicator (As j : Set (List Bool)) V with horacle
  refine ⟨m * K + 2 * m + kD * (2 * cs * K2 + 3),
    compileFinTM (armProg A l₀) (l₀, .start) (bankTM Ms) (bankStart Ms), fun x => ?_⟩
  set n := x.length with hn
  set Ls := logSpace n with hLs
  have hL1 : 1 ≤ Ls := by simp [hLs, logSpace]
  have hLn : Ls ≤ n + 1 := by
    simp only [hLs, logSpace]
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h]; simp
    · have := Nat.log_lt_self 2 (show n ≠ 0 by omega); omega
  set W := K * Ls with hW
  set B := cs * K2 * Ls + 1 with hB
  obtain ⟨N, h1, h2, hm⟩ := hcorr x
  have hpre : ∀ t < N, Pre A oracle (bankTM Ms) (bankStart Ms) B x
      (arun A oracle x (some l₀, fun _ => 0, none) t) ∧
      ∀ r, ((Nat.bits ((arun A oracle x (some l₀, fun _ => 0, none) t).2.1 r + 1)).length : ℤ)
        ≤ (W : ℤ) := by
    intro t ht
    obtain ⟨hps, hbd⟩ := hm t ht
    refine ⟨?_, fun r => by exact_mod_cast hbd r⟩
    generalize hat : arun A oracle x (some l₀, fun _ => 0, none) t = a at hps hbd
    rcases a with ⟨_ | l, v, res⟩
    · trivial
    · simp only [Pre]
      cases hA : A l with
      | jeq r s' l₁ l₀' => simpa [PreS, hA] using hps
      | jeqIn r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqFst r l₁ l₀' => simpa [PreS, hA] using hps
      | jeqSnd r l₁ l₀' => simpa [PreS, hA] using hps
      | inc => trivial
      | dec => trivial
      | clr => trivial
      | half => trivial
      | jz => trivial
      | jodd => trivial
      | ret => trivial
      | valP => trivial
      | valQ => trivial
      | call j md args l₁ l₀' =>
      simp only [PreS, hA] at hps
      refine ⟨hps, ?_⟩
      refine cleanRun_mono (bank_cleanRun Ms As (fun j n => c j * logSpace n) hMs j _) ?_
      have hVl := length_callSegs_le (x := x) ⟨j, md, args, l₁, l₀'⟩ W (fun r => Nat.bits (v r))
        (fun r => by
          show (Nat.bits (v r)).length ≤ W
          have h0 : (Nat.bits (v r + 1)).length ≤ W := hbd r
          have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length := by
            exact length_bits_mono (by omega)
          omega) hps
      have hVQ : (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x fun r => Nat.bits (v r))).length ≤
          Q * (n + 1) ^ 1 + 0 := by
        have : W ≤ K * (n + 1) := Nat.mul_le_mul_left K hLn
        have e : Q * (n + 1) ^ 1 + 0 = (4 + 2 * m) * (n + 1) + 2 * m * (K * (n + 1)) := by
          simp only [hQ]; ring
        rw [e]
        have h5 : m * (2 * W + 2) ≤ 2 * m * (K * (n + 1)) + 2 * m := by
          have := Nat.mul_le_mul_left (2 * m) this
          calc m * (2 * W + 2) = 2 * m * W + 2 * m := by ring
            _ ≤ 2 * m * (K * (n + 1)) + 2 * m := by omega
        have h6 : 2 * m ≤ 2 * m * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
        have h7 : (4 + 2 * m) * (n + 1) = 4 * (n + 1) + 2 * m * (n + 1) := by ring
        omega
      have hlog : logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x fun r => Nat.bits (v r))).length
          ≤ K2 * Ls := by
        have h := hK2 n
        have hm' := Nat.log_mono_right (b := 2) hVQ
        simp only [logSpace, hLs] at h hm' ⊢
        omega
      have hcm : c j * logSpace (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
          fun r => Nat.bits (v r))).length ≤ cs * K2 * Ls := by
        calc _ ≤ c j * (K2 * Ls) := Nat.mul_le_mul_left _ hlog
          _ ≤ cs * (K2 * Ls) := Nat.mul_le_mul_right _ (hcj j)
          _ = cs * K2 * Ls := by ring
      simp only [hB]
      exact max_le (by omega) (by omega)
  obtain ⟨T, hT, hsp⟩ := arm_space A l₀ oracle (bankTM Ms) (bankStart Ms) B W N
    (MultiTapeTM.indicator (L : Set (List Bool)) x) h1 h2 hpre
  refine ⟨T, hT, hsp.trans ?_⟩
  · -- the arithmetic
    show _ ≤ (m * K + 2 * m + kD * (2 * cs * K2 + 3)) * Ls
    have e1 : m * (W + 2) = m * K * Ls + 2 * m := by simp only [hW]; ring
    have e2 : kD * (2 * B + 1) = 2 * kD * cs * K2 * Ls + 3 * kD := by simp only [hB]; ring
    have e3 : (m * K + 2 * m + kD * (2 * cs * K2 + 3)) * Ls =
        m * K * Ls + 2 * m * Ls + 2 * kD * cs * K2 * Ls + 3 * kD * Ls := by ring
    rw [e1, e2, e3]
    have f1 : 2 * m ≤ 2 * m * Ls := Nat.le_mul_of_pos_right _ (by omega)
    have f2 : 3 * kD ≤ 3 * kD * Ls := Nat.le_mul_of_pos_right _ (by omega)
    omega

end Complexity.LogProg
