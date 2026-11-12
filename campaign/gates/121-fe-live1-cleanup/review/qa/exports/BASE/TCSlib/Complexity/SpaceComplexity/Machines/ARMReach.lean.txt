/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMRun

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines reaching live configurations

`Complexity.LogProg.arm_run` follows an abstract register machine until it halts. Here the
compiled program follows it to a *live* configuration instead: if the abstract machine goes
from `(l, v)` to `(l', v')` in `N` steps, with the preconditions and register widths of
`arm_run` along the way, the compiled program goes from the representation of `(l, v)` to
that of `(l', v')` (`Complexity.LogProg.arm_reach`), through configurations satisfying the run
invariant `Complexity.LogProg.Inv`. Composed with `Complexity.LogProg.compile_correct_from`,
this splices compiled runs at arbitrary step boundaries, as needed between the choices of a
nondeterministic machine (`TCSlib.Complexity.SpaceComplexity.Machines.NARMRun`).

This is infrastructure for the register-machine descriptions of space-bounded algorithms of
[AB09, §4.1], not itself a result of the book.

## Main definitions

* none (run theorems for `Complexity.LogProg.ARM`).

## Main results

* `Complexity.LogProg.astep_cases` — one abstract step either moves to a live label, keeping
  the answer slot, or halts with an answer, keeping the registers.
* `Complexity.LogProg.arm_step` — one live abstract step is simulated by the compiled program.
* `Complexity.LogProg.arm_reach` — `N` steps to a live configuration are simulated.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- **The shape of one abstract step**: from a live configuration the machine either moves
to a live label with the answer slot unchanged, or halts with an answer and the registers
unchanged. -/
lemma astep_cases (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (l : Λ)
    (v : Fin m → ℕ) (res : Option Bool) :
    (∃ l' v', astep A oracle x (some l, v, res) = (some l', v', res)) ∨
      ∃ b, astep A oracle x (some l, v, res) = (none, v, some b) := by
  cases hA : A l with
  | ret b => exact Or.inr ⟨b, by simp [astep, hA]⟩
  | valP r l' => by_cases h : ValidPlain x <;> simp [astep, hA, h]
  | valQ r l' => by_cases h : ValidPair x <;> simp [astep, hA, h]
  | _ => simp [astep, hA]

/-- A live abstract step started with an empty answer slot keeps it empty. -/
lemma astep_live_res (A : ARM m d Λ) (oracle : Fin d → List Bool → Bool) (l l' : Λ)
    (v v' : Fin m → ℕ) (res : Option Bool)
    (h : astep A oracle x (some l, v, none) = (some l', v', res)) : res = none := by
  rcases astep_cases (x := x) A oracle l v none with ⟨l'', v'', h'⟩ | ⟨b, h'⟩
  · rw [h'] at h; simp only [Prod.mk.injEq] at h; exact h.2.2.symm
  · rw [h'] at h; simp at h

/-- A simulated run reaching `c'` gives a run to `c'` through configurations satisfying the
run invariant. -/
lemma inv_of_simTo (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) {c c' : Cfg m Bool (Λ × Ph) x}
    (h : SimTo (armProg A l₀) oracle W c c') :
    ∃ T, rrun (armProg A l₀) oracle c T = c' ∧
      ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle c t) := by
  obtain ⟨T, e, hm⟩ := h
  exact ⟨T, e, fun t ht => inv_of_mid A l₀ oracle D q0 B W _ (hm t ht)⟩

/-- **One live abstract step is simulated.** If the abstract machine steps from `(l, v)` to the
live configuration `(l', v')`, with the preconditions `Pre` met and values of at most `W`
binary digits (counting one increment), then the compiled program goes from the
representation of `(l, v)` to that of `(l', v')`, through configurations satisfying `Inv`.

**Proof sketch.** Case analysis on the instruction at `l`, as in `arm_run`: each live step is
one of the simulation lemmas `sim_inc`, …, `sim_jeqFst` (whose intermediate configurations
satisfy `Inv` by `inv_of_mid`), or a single call step (`sim_call`), whose precondition
`CallOK` is `Pre` at a call; the halting instructions cannot step to a live configuration. -/
theorem arm_step (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (l l' : Λ) (v v' : Fin m → ℕ)
    (out : List Bool) (hs : astep A oracle x (some l, v, none) = (some l', v', none))
    (hp : Pre A oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    ∃ T, rrun (armProg A l₀) oracle (aseam x l v out) T = aseam x l' v' out ∧
      ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) := by
  have hW0 : (0 : ℤ) ≤ W := by omega
  have hlen : ∀ r, ((Nat.bits (v r)).length : ℤ) ≤ W := by
    intro r
    have := hw r
    have hle : (Nat.bits (v r)).length ≤ (Nat.bits (v r + 1)).length :=
      length_bits_mono (by omega)
    omega
  have go := fun {c' : Cfg m Bool (Λ × Ph) x} (h : SimTo (armProg A l₀) oracle W
    (aseam x l v out) c') => inv_of_simTo A l₀ oracle D q0 B W h
  cases hA : A l with
  | inc r l'' =>
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_inc A l₀ oracle l l'' r hA v out W (hw r))
  | dec r l'' =>
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_dec A l₀ oracle l l'' r hA v out W (hlen r))
  | clr r l'' =>
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_clr A l₀ oracle l l'' r hA v out W (hlen r))
  | half r l'' =>
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_half A l₀ oracle l l'' r hA v out W (hlen r))
  | jz r l₁ l₀' =>
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_jz A l₀ oracle l l₁ l₀' r hA v out W hW0)
  | jodd r l₁ l₀' =>
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_jodd A l₀ oracle l l₁ l₀' r hA v out W hW0)
  | jeq r s' l₁ l₀' =>
    have hrs : r ≠ s' := by simpa [Pre, hA] using hp
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_jeq A l₀ oracle l l₁ l₀' r s' hrs hA v out W (hlen r))
  | jeqIn r l₁ l₀' =>
    have hx : ValidPlain x := by simpa [Pre, hA] using hp
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_jeqIn A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
  | jeqFst r l₁ l₀' =>
    have hx : ValidPair x := by simpa [Pre, hA] using hp
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_jeqFst A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
  | jeqSnd r l₁ l₀' =>
    have hx : ValidPair x := by simpa [Pre, hA] using hp
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    exact go (sim_jeqSnd A l₀ oracle l l₁ l₀' r hA v out W (hlen r) hx)
  | ret b' => simp [astep, hA] at hs
  | valP r l'' =>
    by_cases hv : ValidPlain x
    · simp only [astep, hA, hv, if_true, Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨rfl, rfl, -⟩ := hs
      exact go ((sim_valP A l₀ oracle l l'' r hA v out W hW0).1 hv)
    · simp [astep, hA, hv] at hs
  | valQ r l'' =>
    by_cases hv : ValidPair x
    · simp only [astep, hA, hv, if_true, Prod.mk.injEq, Option.some.injEq] at hs
      obtain ⟨rfl, rfl, -⟩ := hs
      exact go ((sim_valQ A l₀ oracle l l'' r hA v out W hW0).1 hv)
    · simp [astep, hA, hv] at hs
  | call j md args l₁ l₀' =>
    have hpc : args.Nodup ∧ CleanRun D (q0 j)
        (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))
        (oracle j (vword (callSegs ⟨j, md, args, l₁, l₀'⟩ x (fun r => Nat.bits (v r))))) B := by
      simpa [Pre, hA] using hp
    simp only [astep, hA, Prod.mk.injEq, Option.some.injEq] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    refine ⟨1, sim_call (x := x) A l₀ oracle l l₁ l₀' j md args hA v out, fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    rw [rrun_zero]
    refine ⟨fun r => by simp [aseam], fun l' cs hl hcs => ?_⟩
    simp only [aseam, Option.some.injEq] at hl
    subst hl
    rw [armProg_call, hA] at hcs
    simp only [insCall, Option.some.injEq] at hcs
    subst hcs
    have hwd : regWords (aseam x l v out) = fun r => Nat.bits (v r) := by
      funext r; simp [regWords, aseam, tapeWord_bufferTape]
    refine ⟨hpc.1, rfl, fun r _ => ?_, ?_⟩
    · rw [hwd]; exact ⟨rfl, rfl, le_rfl, hlen r⟩
    · rw [hwd]; exact hpc.2

/-- **The reach theorem for abstract register machines.** If, from `(l, v)`, the abstract
machine is at the live configuration `(l', v')` after `N` steps, every configuration before
having the preconditions `Pre` and values of at most `W` binary digits (counting one
increment), then the compiled program goes from the representation of `(l, v)` having
written `out` to that of `(l', v')` having written `out`, through configurations satisfying
the run invariant `Inv`.

**Proof sketch.** Induction on `N`. A live configuration is reached only through live
configurations (halting is absorbing, `arun_halted`), with the answer slot empty
(`astep_live_res`); the first step is `arm_step`, and the runs are concatenated
(`rrun_add`). -/
theorem arm_reach (A : ARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (l' : Λ) (v' : Fin m → ℕ)
    (out : List Bool) :
    ∀ (N : ℕ) (l : Λ) (v : Fin m → ℕ),
      arun A oracle x (some l, v, none) N = (some l', v', none) →
      (∀ t < N, Pre A oracle D q0 B x (arun A oracle x (some l, v, none) t) ∧
        ∀ r, ((Nat.bits ((arun A oracle x (some l, v, none) t).2.1 r + 1)).length : ℤ) ≤ W) →
      ∃ T, rrun (armProg A l₀) oracle (aseam x l v out) T = aseam x l' v' out ∧
        ∀ t < T, Inv A l₀ oracle D q0 B W (rrun (armProg A l₀) oracle (aseam x l v out) t) := by
  intro N
  induction N with
  | zero =>
    intro l v h _
    simp only [arun, Function.iterate_zero, id, Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨0, rfl, fun t ht => by omega⟩
  | succ N ih =>
    intro l v h hpre
    obtain ⟨hp0, hw0⟩ := hpre 0 (by omega)
    simp only [arun, Function.iterate_zero, id] at hp0 hw0
    rw [arun_succ] at h
    rcases astep_cases (x := x) A oracle l v none with ⟨l₁, v₁, hs⟩ | ⟨b, hs⟩
    · obtain ⟨T₁, e1, m1⟩ := arm_step A l₀ oracle D q0 B W l l₁ v v₁ out hs hp0 hw0
      rw [hs] at h
      obtain ⟨T₂, e2, m2⟩ := ih l₁ v₁ h (fun t ht => by
        have := hpre (t + 1) (by omega); rwa [arun_succ, hs] at this)
      refine ⟨T₁ + T₂, by rw [rrun_add, e1, e2], fun t ht => ?_⟩
      rcases Nat.lt_or_ge t T₁ with h' | h'
      · exact m1 t h'
      · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
        rw [rrun_add, e1]; exact m2 t' (by omega)
    · rw [hs, arun_halted] at h
      simp at h

end Complexity.LogProg
