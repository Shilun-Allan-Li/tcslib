/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines decide in logarithmic space

The run theorem for abstract register machines (`Complexity.LogProg.arm_run`): if the
abstract machine answers `b`, with register values of at most `W` binary digits and the
preconditions of its instructions met, then the compiled machine
(`Complexity.LogProg.compileFinTM` of `Complexity.LogProg.armProg`) answers `b` visiting at
most `m (W + 2) + kD (2B + 1)` work cells (`Complexity.LogProg.arm_space`).

## Main definitions

* `Complexity.LogProg.Pre` — the preconditions of an abstract step.

## Main results

* `Complexity.LogProg.arm_run`, `Complexity.LogProg.arm_space`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The preconditions of the abstract step at a configuration: equality tests compare distinct
registers, index comparisons happen on inputs of the right shape, and a call has distinct
arguments and a decider answering it cleanly within head range `B`. -/
def Pre (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B : ℕ) (x : List Bool) : AConf m Λ → Prop
  | (some l, v, _) =>
    match A l with
    | .jeq r s _ _ => r ≠ s
    | .jeqIn _ _ _ => ValidPlain x
    | .jeqFst _ _ _ => ValidPair x
    | .jeqSnd _ _ _ => ValidPair x
    | .call j md args l₁ l₀ => args.Nodup ∧
        CleanRun D (q0 j) (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))
          (oracle j (vword (callSegs ⟨j, md, args, l₁, l₀⟩ x (fun r => Nat.bits (v r))))) B
    | _ => True
  | _ => True

/-- Running `n + 1` steps is one step followed by `n` steps. -/
lemma arun_succ (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (a : AConf m Λ) (n : ℕ) :
    arun A oracle x a (n + 1) = arun A oracle x (astep A oracle x a) n := by
  simp [arun, Function.iterate_succ_apply]

/-- A halted abstract configuration stays put. -/
lemma arun_halted (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (v : Fin m → ℕ)
    (res : Option Bool) (n : ℕ) : arun A oracle x (none, v, res) n = (none, v, res) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [arun_succ]; exact ih

/-- The invariant of the compiled run: register heads in `[-1, W]`, and the preconditions of
a call at call nodes. -/
def Inv (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B : ℕ) (W : ℕ) (c : Cfg m Bool (Λ × Ph) x) : Prop :=
  (∀ r, (-1 : ℤ) ≤ c.workTapePos r ∧ c.workTapePos r ≤ W) ∧
    CallOK (armProg A l₀) D q0 oracle (fun _ => -1) (fun _ => (W : ℤ)) B c

/-- A configuration in the middle of an instruction fragment satisfies the run invariant. -/
lemma inv_of_mid (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (c : Cfg m Bool (Λ × Ph) x)
    (h : Mid (armProg A l₀) W c) : Inv A l₀ oracle D q0 B W c := by
  refine ⟨h.2, fun l cs hl hcs => ?_⟩
  rw [h.1 l hl] at hcs; simp at hcs

/-- Compose a simulated run with a continuation.

**Proof sketch.** Concatenate the two runs (`rrun_add`). Times before the end of the simulated
run satisfy the invariant by `inv_of_mid` (they are in the middle of a fragment), and later
times by the continuation's hypothesis. -/
lemma inv_append (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (c c' : Cfg m Bool (Λ × Ph) x)
    (h₁ : SimTo (armProg A l₀) oracle W c c') (out : List Bool) (b : Bool)
    (h₂ : ∃ T, (rrun (armProg A l₀) oracle c' T).state = none ∧
      (rrun (armProg A l₀) oracle c' T).output = out ++ [b] ∧
      (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle c' T).workTapePos r ∧
        (rrun (armProg A l₀) oracle c' T).workTapePos r ≤ W) ∧
      ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle c' t)) :
    ∃ T, (rrun (armProg A l₀) oracle c T).state = none ∧
      (rrun (armProg A l₀) oracle c T).output = out ++ [b] ∧
      (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle c T).workTapePos r ∧
        (rrun (armProg A l₀) oracle c T).workTapePos r ≤ W) ∧
      ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle c t) := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, f3, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [rrun_add, e1]; exact f1, by rw [rrun_add, e1]; exact f2,
    by rw [rrun_add, e1]; exact f3, fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact inv_of_mid A l₀ oracle D q0 B W _ (m1 t h)
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [rrun_add, e1]; exact m2 t' (by omega)

/-- **The run theorem for abstract register machines.** If, from `l` with values `v`, the
abstract machine halts after `N` steps with answer `b`, every configuration before has the
preconditions `Pre` and values of at most `W` binary digits (counting one increment), then
the compiled program, from the representation of `(l, v)` having written `out`, halts with
`out ++ [b]`, its register heads in `[-1, W]` and its calls meeting `CallOK`.

**Proof sketch.** Induction on `N`; each abstract step is one of the simulation lemmas
`sim_inc`, …, `sim_jeqFst` of `TCSlib.Complexity.SpaceComplexity.Machines.ARMSim`. -/
theorem arm_run (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) :
    ∀ (N : ℕ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) (b : Bool),
      (arun A oracle x (some l, v, none) N).1 = none →
      (arun A oracle x (some l, v, none) N).2.2 = some b →
      (∀ t < N, Pre A oracle D q0 B x (arun A oracle x (some l, v, none) t) ∧
        ∀ r, ((Nat.bits ((arun A oracle x (some l, v, none) t).2.1 r + 1)).length : ℤ) ≤ W) →
      ∃ T, (rrun (armProg A l₀) oracle (aseam x l v out) T).state = none ∧
        (rrun (armProg A l₀) oracle (aseam x l v out) T).output = out ++ [b] ∧
        (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ∧
          (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ≤ W) ∧
        ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) := by
  intro N
  induction N with
  | zero => intro l v out b h1 _ _; simp [arun] at h1
  | succ N ih =>
    intro l v out b h1 h2 hpre
    obtain ⟨hp0, hb0⟩ := hpre 0 (by omega)
    simp only [arun, Function.iterate_zero, id] at hp0 hb0
    have hW0 : (0 : ℤ) ≤ W := by omega
    have hlen : ∀ r, ((Nat.bits (v r)).length : ℤ) ≤ W := by
      intro r
      have := hb0 r
      have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length := by
        exact length_bits_mono (by omega)
      omega
    -- the continuation after the first abstract step
    have cont : ∀ (l' : Λ) (v' : Fin m → ℕ), astep A oracle x (some l, v, none) = (some l', v', none) →
        ∃ T, (rrun (armProg A l₀) oracle (aseam x l' v' out) T).state = none ∧
          (rrun (armProg A l₀) oracle (aseam x l' v' out) T).output = out ++ [b] ∧
          (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l' v' out) T).workTapePos r ∧
            (rrun (armProg A l₀) oracle (aseam x l' v' out) T).workTapePos r ≤ W) ∧
          ∀ t < T, Inv A l₀ oracle D q0 B W
            (rrun (armProg A l₀) oracle (aseam x l' v' out) t) := by
      intro l' v' hs
      rw [arun_succ, hs] at h1 h2
      exact ih l' v' out b h1 h2 (fun t ht => by
        have := hpre (t + 1) (by omega); rwa [arun_succ, hs] at this)
    -- a halting first step
    have halt : ∀ (b' : Bool), astep A oracle x (some l, v, none) = (none, v, some b') → b' = b := by
      intro b' hs
      rw [arun_succ, hs, arun_halted] at h2
      simpa using h2
    have haltW : ∀ (b' : Bool), HaltsWith (armProg A l₀) oracle W (aseam x l v out) b' →
        b' = b → ∃ T, (rrun (armProg A l₀) oracle (aseam x l v out) T).state = none ∧
          (rrun (armProg A l₀) oracle (aseam x l v out) T).output = out ++ [b] ∧
          (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ∧
            (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ≤ W) ∧
          ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) := by
      rintro b' ⟨T, e1, e2, e3, hm⟩ rfl
      exact ⟨T, e1, e2, e3, fun t ht => inv_of_mid A l₀ oracle D q0 B W _ (hm t ht)⟩
    have step : ∀ (l' : Λ) (v' : Fin m → ℕ), astep A oracle x (some l, v, none) = (some l', v', none) →
        SimTo (armProg A l₀) oracle W (aseam x l v out) (aseam x l' v' out) →
        ∃ T, (rrun (armProg A l₀) oracle (aseam x l v out) T).state = none ∧
          (rrun (armProg A l₀) oracle (aseam x l v out) T).output = out ++ [b] ∧
          (∀ r, (-1 : ℤ) ≤ (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ∧
            (rrun (armProg A l₀) oracle (aseam x l v out) T).workTapePos r ≤ W) ∧
          ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) :=
      fun l' v' hs hsim => inv_append A l₀ oracle D q0 B W _ _ hsim out b (cont l' v' hs)
    cases hA : A l with
    | inc r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_inc A l₀ oracle l l' r hA v out W (hb0 r))
    | dec r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_dec A l₀ oracle l l' r hA v out W (hlen r))
    | clr r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_clr A l₀ oracle l l' r hA v out W (hlen r))
    | half r l' =>
      exact step _ _ (by simp [astep, hA]) (sim_half A l₀ oracle l l' r hA v out W (hlen r))
    | jz r l₁ l₀' =>
      exact step _ _ (by simp [astep, hA]) (sim_jz A l₀ oracle l l₁ l₀' r hA v out W hW0)
    | jodd r l₁ l₀' =>
      exact step _ _ (by simp [astep, hA]) (sim_jodd A l₀ oracle l l₁ l₀' r hA v out W hW0)
    | jeq r s' l₁ l₀' =>
      have hrs : r ≠ s' := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA])
        (sim_jeq A l₀ oracle l l₁ l₀' r s' hrs hA v out W (hlen r))
    | jeqIn r l₁ l₀' =>
      have hx : ValidPlain x := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA]) (sim_jeqIn A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
    | jeqFst r l₁ l₀' =>
      have hx : ValidPair x := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA])
        (sim_jeqFst A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
    | jeqSnd r l₁ l₀' =>
      have hx : ValidPair x := by simpa [Pre, hA] using hp0
      exact step _ _ (by simp [astep, hA])
        (sim_jeqSnd A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
    | ret b' =>
      exact haltW b' (sim_ret A l₀ oracle l b' hA v out W hW0) (halt b' (by simp [astep, hA]))
    | valP r l' =>
      obtain ⟨s1, s2⟩ := sim_valP A l₀ oracle l l' r hA v out W hW0
      by_cases hv : ValidPlain x
      · exact step _ _ (by simp [astep, hA, hv]) (s1 hv)
      · exact haltW false (s2 hv) (halt false (by simp [astep, hA, hv]))
    | valQ r l' =>
      obtain ⟨s1, s2⟩ := sim_valQ A l₀ oracle l l' r hA v out W hW0
      by_cases hv : ValidPair x
      · exact step _ _ (by simp [astep, hA, hv]) (s1 hv)
      · exact haltW false (s2 hv) (halt false (by simp [astep, hA, hv]))
    | call j md args l₁ l₀' =>
      have hpc : args.Nodup ∧ CleanRun D (q0 j)
          (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))
          (oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))) B := by
        simpa [Pre, hA] using hp0
      have h1s := sim_call (x := x) A l₀ oracle l l₁ l₀' j md args hA v out
      obtain ⟨T, f1, f2, f3, hm⟩ := cont (if oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x
        (fun r => Nat.bits (v r)))) then l₁ else l₀') v (by simp [astep, hA])
      refine ⟨1 + T, by rw [rrun_add, h1s]; exact f1, by rw [rrun_add, h1s]; exact f2,
        by rw [rrun_add, h1s]; exact f3, fun t ht => ?_⟩
      rcases Nat.lt_or_ge t 1 with h | h
      · obtain rfl : t = 0 := by omega
        rw [rrun_zero]
        refine ⟨fun r => by simp [aseam], fun l' cs hl hcs => ?_⟩
        simp only [aseam, Option.some.injEq] at hl
        subst hl
        rw [armProg_call, hA] at hcs
        simp only [insCall, Option.some.injEq] at hcs
        subst hcs
        have hw : regWords (aseam x l v out) = fun r => Nat.bits (v r) := by
          funext r; simp [regWords, aseam, tapeWord_bufferTape]
        refine ⟨hpc.1, rfl, fun r _ => ?_, ?_⟩
        · rw [hw]; exact ⟨rfl, rfl, le_rfl, hlen r⟩
        · rw [hw]; exact hpc.2
      · obtain ⟨t', rfl⟩ : ∃ t', t = 1 + t' := ⟨t - 1, by omega⟩
        rw [rrun_add, h1s]; exact hm t' (by omega)

/-- The initial configuration of the compiled program is the program configuration of the
start label with all registers `0` and empty output. -/
lemma init_eq_aseam (l₀ : Λ) : (Cfg.init (k := m) (l₀, Ph.start) x) = aseam x l₀ (fun _ => 0) [] := by
  refine Cfg.ext rfl rfl ?_ rfl rfl
  funext r z; simp [aseam, Nat.zero_bits]

/-- **Abstract register machines decide in small space.** If the abstract machine, started at
`l₀` with all registers `0`, answers `b` on input `x` after `N` steps, with the
preconditions met and all values of at most `W` binary digits (counting one increment), then
the compiled machine outputs `[b]` on `x`, visiting at most `m (W + 2) + kD (2B + 1)` work
cells.

**Proof sketch.** `arm_run` from the initial configuration (`init_eq_aseam`), then
`compile_space` with register ranges `[-1, W]`. -/
theorem arm_space [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD] (A : ARM m d Λ)
    (l₀ : Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (B W N : ℕ) (b : Bool)
    (h1 : (arun A oracle x (some l₀, fun _ => 0, none) N).1 = none)
    (h2 : (arun A oracle x (some l₀, fun _ => 0, none) N).2.2 = some b)
    (hpre : ∀ t < N, Pre A oracle D q0 B x (arun A oracle x (some l₀, fun _ => 0, none) t) ∧
      ∀ r, ((Nat.bits ((arun A oracle x (some l₀, fun _ => 0, none) t).2.1 r + 1)).length : ℤ) ≤ W) :
    ∃ T, (compileFinTM (armProg A l₀) (l₀, .start) D q0).ComputesInTime x [b] T ∧
      (compileFinTM (armProg A l₀) (l₀, .start) D q0).tm.spaceUsed
        ((compileFinTM (armProg A l₀) (l₀, .start) D q0).tm.initCfg x) T ≤
        m * (W + 2) + kD * (2 * B + 1) := by
  obtain ⟨T, e1, e2, e3, hm⟩ := arm_run A l₀ oracle D q0 B W N l₀ (fun _ => 0) [] b h1 h2 hpre
  rw [← init_eq_aseam] at e1 e2 e3 hm
  simp only [List.nil_append] at e2
  obtain ⟨T', hT', hsp⟩ := compile_space (armProg A l₀) (l₀, .start) D q0 oracle (fun _ => -1)
    (fun _ => (W : ℤ)) B T [b] e1 e2
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hm t h).1 r
      · obtain rfl : t = T := by omega
        exact e3 r)
    (fun t ht => (hm t ht).2)
  refine ⟨T', hT', hsp.trans (le_of_eq ?_)⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  congr 2

end Complexity.LogProg
