/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops
import TCSlib.Complexity.SpaceComplexity.Machines.ARMReach

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Abstract register machines with a monotone memory tape

A *memory register machine* (`Complexity.LogProg.MARM`) is an abstract register machine
(`Complexity.LogProg.ARM`) with one more device: a tape of bits (the *memory*), initially all
`0`, with a head, and four more instructions: branch on the bit under the head (`mread`), set
it to `1` (`mset`), and move the head (`mleft`, `mright`). Bits are never reset, so the
memory only grows. This is what an exponential-time algorithm needs beyond the counters of
a space-bounded one: a table indexed by register values (a visited set, [AB09, §4.1.1,
proof of Theorem 4.2]), addressed by walking the head. The compiled machine is in
`TCSlib.Complexity.SpaceComplexity.Machines.MARMCompile`, its time bound in
`TCSlib.Complexity.SpaceComplexity.Machines.MARMTime`.

Runs of a memory register machine between memory instructions are runs of its
*deterministic part* (`Complexity.LogProg.MARM.detPart`, answering a fixed bit at the memory
labels), so the counting loops of `TCSlib.Complexity.SpaceComplexity.Machines.ARMLoops` and
`TCSlib.Complexity.SpaceComplexity.Logspace.InputAccess` transfer
(`Complexity.LogProg.MReach.of_areach`).

The machine model is infrastructure for [AB09, §4.1.1], not itself a result of the book.

## Main definitions

* `Complexity.LogProg.MIns`, `Complexity.LogProg.MARM` — instructions and machines.
* `Complexity.LogProg.MARM.detPart` — the register instructions, `ret β` at memory labels.
* `Complexity.LogProg.mstep`, `Complexity.LogProg.mrun` — the semantics.
* `Complexity.LogProg.MReach`, `Complexity.LogProg.MHalt` — runs through a guard.

## Main results

* the run algebra `mrun_add`, `MReach.trans`, `MReach.halt`, `MReach.step`, `MHalt.step`,
  `MHalt.ret`;
* `Complexity.LogProg.MReach.of_areach` — a run of the deterministic part to a live
  configuration is a run of the memory machine, the memory untouched.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1, Theorem 4.2.)
-/

namespace Complexity.LogProg

open Turing

variable {m d : ℕ} {Λ : Type} {x : List Bool}

/-- The instructions of a memory register machine: a register instruction, or a memory
instruction. -/
inductive MIns (m d : ℕ) (Λ : Type) where
  /-- a register instruction of `Complexity.LogProg.Ins` -/
  | det (i : Ins m d Λ)
  /-- go to `l₁` if the memory bit under the head is `1`, else to `l₀` -/
  | mread (l₁ l₀ : Λ)
  /-- set the memory bit under the head to `1` -/
  | mset (l : Λ)
  /-- move the memory head one cell left -/
  | mleft (l : Λ)
  /-- move the memory head one cell right -/
  | mright (l : Λ)

/-- A memory register machine: an instruction at every label. -/
abbrev MARM (m d : ℕ) (Λ : Type) := Λ → MIns m d Λ

/-- Whether an instruction is a memory instruction. -/
def MIns.isMem {m d : ℕ} {Λ : Type} : MIns m d Λ → Bool
  | .det _ => false
  | _ => true

/-- The deterministic part of a memory register machine, answering `β` at the memory labels.
The compiled memory machine agrees with the compiled `A.detPart β` away from those labels. -/
def MARM.detPart (A : MARM m d Λ) (β : Bool) : ARM m d Λ := fun l =>
  match A l with
  | .det i => i
  | _ => .ret β

/-- At a register label the deterministic part is the instruction. -/
lemma MARM.detPart_det {A : MARM m d Λ} {l : Λ} {i : Ins m d Λ} (hA : A l = .det i)
    (β : Bool) : A.detPart β l = i := by
  simp [MARM.detPart, hA]

/-- At a memory label the deterministic part answers `β`. -/
lemma MARM.detPart_mem {A : MARM m d Λ} {l : Λ} (hA : (A l).isMem = true) (β : Bool) :
    A.detPart β l = .ret β := by
  unfold MARM.detPart
  cases h : A l with
  | det i => rw [h] at hA; simp [MIns.isMem] at hA
  | _ => rfl

/-- The memory: the bits (`true` = `1`) and the head position. -/
abbrev Mem := (ℤ → Bool) × ℤ

/-- A configuration of a memory register machine: an abstract configuration and the memory. -/
abbrev MConf (m : ℕ) (Λ : Type) := AConf m Λ × Mem

open Classical in
/-- **One step of a memory register machine** on input `x`, deciders answering `oracle`: a
register instruction acts as in `astep` on the abstract configuration, a memory instruction on
the memory; halted configurations are fixed. -/
noncomputable def mstep (A : MARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) : MConf m Λ → MConf m Λ
  | ((none, v, res), μ) => ((none, v, res), μ)
  | ((some l, v, res), (M, p)) =>
    match A l with
    | .det i => (astep (fun _ => i) oracle x (some l, v, res), (M, p))
    | .mread l₁ l₀ => ((some (if M p then l₁ else l₀), v, res), (M, p))
    | .mset l' => ((some l', v, res), (Function.update M p true, p))
    | .mleft l' => ((some l', v, res), (M, p - 1))
    | .mright l' => ((some l', v, res), (M, p + 1))

/-- The run of a memory register machine. -/
noncomputable def mrun (A : MARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (c : MConf m Λ) (n : ℕ) : MConf m Λ :=
  (mstep A oracle x)^[n] c

/-- A run of a memory register machine from `a` to `a'` through configurations satisfying
`G`. -/
def MReach (A : MARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : MConf m Λ → Prop) (a a' : MConf m Λ) : Prop :=
  ∃ T, mrun A oracle x a T = a' ∧ ∀ t < T, G (mrun A oracle x a t)

/-- A run of a memory register machine from `a` answering `b`, through configurations
satisfying `G`. -/
def MHalt (A : MARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : MConf m Λ → Prop) (a : MConf m Λ) (b : Bool) : Prop :=
  ∃ T, (mrun A oracle x a T).1.1 = none ∧ (mrun A oracle x a T).1.2.2 = some b ∧
    ∀ t < T, G (mrun A oracle x a t)

section Semantics

variable {A : MARM m d Λ} {oracle : Fin d → List Bool → Bool}

/-- At a register label a step is the step of the deterministic part, the memory untouched. -/
lemma mstep_det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (β : Bool) (v : Fin m → ℕ)
    (res : Option Bool) (μ : Mem) :
    mstep A oracle x ((some l, v, res), μ) =
      (astep (A.detPart β) oracle x (some l, v, res), μ) := by
  obtain ⟨M, p⟩ := μ
  simp only [mstep, hA, astep, MARM.detPart_det hA β]

/-- Running `n + 1` steps is one step followed by `n` steps. -/
lemma mrun_succ (c : MConf m Λ) (n : ℕ) :
    mrun A oracle x c (n + 1) = mrun A oracle x (mstep A oracle x c) n := by
  simp [mrun, Function.iterate_succ_apply]

/-- Running `s + t` steps is running `s` steps, then `t` steps. -/
lemma mrun_add (c : MConf m Λ) (s t : ℕ) :
    mrun A oracle x c (s + t) = mrun A oracle x (mrun A oracle x c s) t := by
  simp only [mrun]; rw [Nat.add_comm, Function.iterate_add_apply]

/-- A halted configuration stays put. -/
lemma mrun_halted (v : Fin m → ℕ) (res : Option Bool) (μ : Mem) (n : ℕ) :
    mrun A oracle x ((none, v, res), μ) n = ((none, v, res), μ) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [mrun_succ]; exact ih

end Semantics

section Combinators

variable {A : MARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : MConf m Λ → Prop}

/-- Every configuration reaches itself. -/
lemma MReach.refl (a : MConf m Λ) : MReach A oracle x G a a := ⟨0, rfl, fun t h => by omega⟩

/-- Runs compose. -/
lemma MReach.trans {a b c : MConf m Λ} (h₁ : MReach A oracle x G a b)
    (h₂ : MReach A oracle x G b c) : MReach A oracle x G a c := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, e2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [mrun_add, e1, e2], fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [mrun_add, e1]; exact m2 t' (by omega)

/-- A run followed by a halting run is a halting run with the same answer. -/
lemma MReach.halt {a b : MConf m Λ} {r : Bool} (h₁ : MReach A oracle x G a b)
    (h₂ : MHalt A oracle x G b r) : MHalt A oracle x G a r := by
  obtain ⟨T₁, e1, m1⟩ := h₁
  obtain ⟨T₂, f1, f2, m2⟩ := h₂
  refine ⟨T₁ + T₂, by rw [mrun_add, e1]; exact f1, by rw [mrun_add, e1]; exact f2,
    fun t ht => ?_⟩
  rcases Nat.lt_or_ge t T₁ with h | h
  · exact m1 t h
  · obtain ⟨t', rfl⟩ : ∃ t', t = T₁ + t' := ⟨t - T₁, by omega⟩
    rw [mrun_add, e1]; exact m2 t' (by omega)

/-- A configuration satisfying the guard reaches its successor in one step. -/
lemma MReach.single {a : MConf m Λ} (hG : G a) :
    MReach A oracle x G a (mstep A oracle x a) := ⟨1, rfl, fun t ht => by
  obtain rfl : t = 0 := by omega
  exact hG⟩

/-- A step followed by a run. -/
lemma MReach.step {a c : MConf m Λ} (hG : G a) (h : MReach A oracle x G (mstep A oracle x a) c) :
    MReach A oracle x G a c := (MReach.single hG).trans h

/-- A step followed by a halting run. -/
lemma MHalt.step {a : MConf m Λ} {r : Bool} (hG : G a)
    (h : MHalt A oracle x G (mstep A oracle x a) r) : MHalt A oracle x G a r :=
  (MReach.single hG).halt h

/-- Answering in one step. -/
lemma MHalt.ret {l : Λ} {v : Fin m → ℕ} {r : Bool} {μ : Mem} (hA : A l = .det (.ret r))
    (hG : G ((some l, v, none), μ)) : MHalt A oracle x G ((some l, v, none), μ) r :=
  ⟨1, by obtain ⟨M, p⟩ := μ; simp [mrun, mstep, astep, hA],
    by obtain ⟨M, p⟩ := μ; simp [mrun, mstep, astep, hA], fun t ht => by
    obtain rfl : t = 0 := by omega
    exact hG⟩

/-- Rewriting the end configuration of a run along an equation. -/
lemma MReach.of_eq {a b b' : MConf m Λ} (h : MReach A oracle x G a b) (e : b = b') :
    MReach A oracle x G a b' := e ▸ h

/-- A run through a guard is a run through any weaker guard. -/
lemma MReach.mono {G' : MConf m Λ → Prop} {a b : MConf m Λ} (h : MReach A oracle x G a b)
    (hG : ∀ c, G c → G' c) : MReach A oracle x G' a b := by
  obtain ⟨T, e, hm⟩ := h; exact ⟨T, e, fun t ht => hG _ (hm t ht)⟩

/-- A halting run through a guard is a halting run through any weaker guard. -/
lemma MHalt.mono {G' : MConf m Λ → Prop} {a : MConf m Λ} {r : Bool}
    (h : MHalt A oracle x G a r) (hG : ∀ c, G c → G' c) : MHalt A oracle x G' a r := by
  obtain ⟨T, e1, e2, hm⟩ := h; exact ⟨T, e1, e2, fun t ht => hG _ (hm t ht)⟩

end Combinators

section Transfer

variable {A : MARM m d Λ} {oracle : Fin d → List Bool → Bool}

/-- A run of the deterministic part from `a` that is live at time `T` is, up to time `T`, a
run of the memory machine with the memory untouched.

**Proof sketch.** Induction on the time. A live run never visits a memory label before its
end: there the deterministic part answers and halts for good (`arun_halted`). At register
labels the two steps agree (`mstep_det`); halted configurations are fixed by both. -/
lemma mrun_eq_arun (β : Bool) (a : AConf m Λ) (μ : Mem) (T : ℕ)
    (hlive : (arun (A.detPart β) oracle x a T).1 ≠ none) :
    ∀ t ≤ T, mrun A oracle x (a, μ) t = (arun (A.detPart β) oracle x a t, μ) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have e := ih (by omega)
    rw [mrun_add, e]
    show mstep A oracle x _ = _
    rw [show arun (A.detPart β) oracle x a (t + 1) =
      astep (A.detPart β) oracle x (arun (A.detPart β) oracle x a t) by
        simp [arun, Function.iterate_succ_apply']]
    generalize hc : arun (A.detPart β) oracle x a t = c
    obtain ⟨_ | l, v, res⟩ := c
    · rfl
    · cases hA : A l with
      | det i => exact mstep_det hA β v res μ
      | _ =>
        exfalso
        have hret : A.detPart β l = .ret β := MARM.detPart_mem (by simp [hA, MIns.isMem]) β
        have h1 : arun (A.detPart β) oracle x a (t + 1) = (none, v, some β) := by
          simp [arun, Function.iterate_succ_apply'] at hc ⊢
          rw [hc]; simp [astep, hret]
        apply hlive
        rw [show T = (t + 1) + (T - (t + 1)) by omega, arun_add, h1, arun_halted]

/-- **Runs of the deterministic part transfer.** A run of `A.detPart β` through `G` from `a`
to a live configuration `a'` is a run of the memory machine from `(a, μ)` to `(a', μ)` through
configurations whose abstract part satisfies `G` and whose memory is `μ`.

**Proof sketch.** `mrun_eq_arun` up to the end of the run. -/
lemma MReach.of_areach {β : Bool} {G : AConf m Λ → Prop} {a a' : AConf m Λ} (μ : Mem)
    (h : AReach (A.detPart β) oracle x G a a') (hlive : a'.1 ≠ none) :
    MReach A oracle x (fun c => G c.1 ∧ c.2 = μ) (a, μ) (a', μ) := by
  obtain ⟨T, e, hm⟩ := h
  have key := mrun_eq_arun (A := A) (oracle := oracle) (x := x) β a μ T (by rw [e]; exact hlive)
  refine ⟨T, by rw [key T le_rfl, e], fun t ht => ?_⟩
  rw [key t ht.le]
  exact ⟨hm t ht, rfl⟩

end Transfer

end Complexity.LogProg
