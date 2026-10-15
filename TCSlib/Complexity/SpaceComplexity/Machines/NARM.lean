/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.ARMProof
import TCSlib.Complexity.SpaceComplexity.Machines.ARMReach

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Nondeterministic abstract register machines

A *nondeterministic abstract register machine* (`Complexity.LogProg.NARM`) is an abstract
register machine (`Complexity.LogProg.ARM`) with one more instruction, `choose l₁ l₀`: go to
`l₁` or to `l₀`, nondeterministically. Its runs are indexed by *choice words* — one bit per
step, consumed left to right, ignored by the deterministic instructions — exactly as the runs
of the binary-choice machines `Turing.NDTM` [AB09, §2.1.2]. This is how nondeterministic
logspace algorithms are described in [AB09, §4.3] ("guess the next vertex"); the compilation
onto `Turing.FinNDTM` is in `TCSlib.Complexity.SpaceComplexity.Machines.NARMCompile` and the
space theorem in `TCSlib.Complexity.SpaceComplexity.Machines.NARMRun`, the bridges to `NL` and
`NPSPACE` in `TCSlib.Complexity.SpaceComplexity.Machines.NARMProof`.

The machine model is infrastructure for [AB09, §4.1–4.3], not itself a result of the book.

## Main definitions

* `Complexity.LogProg.NIns`, `Complexity.LogProg.NARM` — instructions and machines.
* `Complexity.LogProg.NARM.detPart` — the deterministic machine answering `β` at the
  `choose` labels (used by the compilation).
* `Complexity.LogProg.nastep`, `Complexity.LogProg.narun` — the semantics under choice bits
  and choice words.
* `Complexity.LogProg.NPreS`, `Complexity.LogProg.NPre` — the preconditions of a step.
* `Complexity.LogProg.NHalts` — every choice word of a given length halts the machine through
  configurations satisfying a guard; `Complexity.LogProg.NAns` — some choice word of that
  length ends with a given answer.

## Main results

* `Complexity.LogProg.narun_append`, `Complexity.LogProg.narun_halted` — the run algebra.
* the combinators `Complexity.LogProg.NHalts.det`, `NHalts.choose`, `NHalts.run`,
  `NHalts.mono_len` (and their converses `NHalts.of_det`, `NHalts.of_choose`), and
  `Complexity.LogProg.nans_det`, `nans_choose`, `nans_run`, `nans_mono_len`, for proving
  machines correct by induction over their loops.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, §4.1, §4.3.)
-/

namespace Complexity.LogProg

open Turing

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- The instructions of a nondeterministic abstract register machine: a deterministic
instruction, or a nondeterministic branch. -/
inductive NIns (m d : ℕ) (Λ : Type) where
  /-- a deterministic instruction of `Complexity.LogProg.Ins` -/
  | det (i : Ins m d Λ)
  /-- go to `l₁` (choice bit `1`) or to `l₀` (choice bit `0`) -/
  | choose (l₁ l₀ : Λ)

/-- A nondeterministic abstract register machine: an instruction at every label. -/
abbrev NARM (m d : ℕ) (Λ : Type) := Λ → NIns m d Λ

/-- The branch targets of a `choose` instruction (`none` for a deterministic one). -/
def NIns.targets {m d : ℕ} {Λ : Type} : NIns m d Λ → Option (Λ × Λ)
  | .det _ => none
  | .choose l₁ l₀ => some (l₁, l₀)

/-- The deterministic part of a nondeterministic machine, answering `β` at the `choose`
labels. The compiled nondeterministic machine agrees with the compiled `A.detPart β` away from
the `choose` labels. -/
def NARM.detPart (A : NARM m d Λ) (β : Bool) : ARM m d Λ := fun l =>
  match A l with
  | .det i => i
  | .choose _ _ => .ret β

/-- At a deterministic label the deterministic part is the instruction. -/
lemma NARM.detPart_det {A : NARM m d Λ} {l : Λ} {i : Ins m d Λ} (hA : A l = .det i)
    (β : Bool) : A.detPart β l = i := by
  simp [NARM.detPart, hA]

/-- At a `choose` label the deterministic part answers `β`. -/
lemma NARM.detPart_choose {A : NARM m d Λ} {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀)
    (β : Bool) : A.detPart β l = .ret β := by
  simp [NARM.detPart, hA]

open Classical in
/-- **One step of a nondeterministic abstract register machine** under the choice bit `b`: a
deterministic instruction behaves as in `astep` (ignoring `b`), `choose l₁ l₀` moves to `l₁`
if `b` and to `l₀` otherwise, keeping the values; halted configurations are fixed. -/
noncomputable def nastep (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) (b : Bool) : AConf m Λ → AConf m Λ
  | (none, v, res) => (none, v, res)
  | (some l, v, res) =>
    match A l with
    | .det i => astep (fun _ => i) oracle x (some l, v, res)
    | .choose l₁ l₀ => (some (if b then l₁ else l₀), v, res)

/-- The run of a nondeterministic abstract register machine under a choice word, one bit per
step, consumed left to right. -/
noncomputable def narun (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (x : List Bool) : List Bool → AConf m Λ → AConf m Λ
  | [], a => a
  | b :: σ, a => narun A oracle x σ (nastep A oracle x b a)

/-- The syntactic preconditions of a nondeterministic step: those of the deterministic
instruction (`PreS`), none at a `choose`. -/
def NPreS (A : NARM m d Λ) (x : List Bool) (a : AConf m Λ) : Prop :=
  PreS (A.detPart false) x a

/-- The preconditions of a nondeterministic step: those of the deterministic instruction
(`Pre`, including clean decider runs within head range `B`), none at a `choose`. -/
def NPre (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (B : ℕ) (x : List Bool) (a : AConf m Λ) : Prop :=
  Pre (A.detPart false) oracle D q0 B x a

section Semantics

variable {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool}

/-- At a deterministic label a nondeterministic step is the step of the deterministic part,
whatever the choice bit. -/
lemma nastep_det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (β b : Bool) (v : Fin m → ℕ)
    (res : Option Bool) :
    nastep A oracle x b (some l, v, res) = astep (A.detPart β) oracle x (some l, v, res) := by
  simp only [nastep, hA, astep, NARM.detPart_det hA β]

/-- At a `choose` label a nondeterministic step follows the choice bit. -/
lemma nastep_choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) (b : Bool) (v : Fin m → ℕ)
    (res : Option Bool) :
    nastep A oracle x b (some l, v, res) = (some (if b then l₁ else l₀), v, res) := by
  simp only [nastep, hA]

/-- A halted configuration is fixed by every nondeterministic step. -/
@[simp] lemma nastep_none (b : Bool) (v : Fin m → ℕ) (res : Option Bool) :
    nastep A oracle x b (none, v, res) = (none, v, res) := rfl

/-- The empty choice word runs no step. -/
@[simp] lemma narun_nil (a : AConf m Λ) : narun A oracle x [] a = a := rfl

/-- Consuming one choice bit is one step. -/
lemma narun_cons (b : Bool) (σ : List Bool) (a : AConf m Λ) :
    narun A oracle x (b :: σ) a = narun A oracle x σ (nastep A oracle x b a) := rfl

/-- Running under `σ ++ τ` is running under `σ`, then under `τ`. -/
lemma narun_append (σ τ : List Bool) (a : AConf m Λ) :
    narun A oracle x (σ ++ τ) a = narun A oracle x τ (narun A oracle x σ a) := by
  induction σ generalizing a with
  | nil => rfl
  | cons b σ ih => exact ih _

/-- A halted configuration stays put under every choice word. -/
@[simp] lemma narun_halted (σ : List Bool) (v : Fin m → ℕ) (res : Option Bool) :
    narun A oracle x σ (none, v, res) = (none, v, res) := by
  induction σ with
  | nil => rfl
  | cons b σ ih => exact ih

/-- A configuration halted under a prefix stays put under any extension. -/
lemma narun_append_of_halted {σ : List Bool} {a : AConf m Λ}
    (h : (narun A oracle x σ a).1 = none) (τ : List Bool) :
    narun A oracle x (σ ++ τ) a = narun A oracle x σ a := by
  rw [narun_append]
  obtain ⟨⟨_ | l, v, res⟩, e⟩ : ∃ c, narun A oracle x σ a = c := ⟨_, rfl⟩
  · rw [e, narun_halted]
  · rw [e] at h; simp at h

/-- The preconditions of the deterministic part do not depend on the answer at the `choose`
labels. -/
lemma pre_detPart (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B : ℕ) (β : Bool)
    (a : AConf m Λ) : Pre (A.detPart β) oracle D q0 B x a ↔ NPre A oracle D q0 B x a := by
  rcases a with ⟨_ | l, v, res⟩
  · exact Iff.rfl
  · unfold NPre
    cases hA : A l with
    | det i => simp only [Pre, NARM.detPart_det hA]
    | choose l₁ l₀ => simp only [Pre, NARM.detPart_choose hA]

/-- **A deterministic run inside a nondeterministic machine.** If the deterministic part runs
`T` steps from `a` without meeting a `choose` label (before time `T`), then every choice word
of length at most `T` drives the nondeterministic machine along the same run. -/
lemma narun_eq_arun (β : Bool) (a : AConf m Λ) (T : ℕ)
    (hdet : ∀ t < T, ∀ l, (arun (A.detPart β) oracle x a t).1 = some l → (A l).targets = none)
    (σ : List Bool) (hσ : σ.length ≤ T) :
    narun A oracle x σ a = arun (A.detPart β) oracle x a σ.length := by
  induction σ generalizing a T with
  | nil => rfl
  | cons b σ ih =>
    obtain ⟨T, rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by simp at hσ; omega⟩
    have hstep : nastep A oracle x b a = astep (A.detPart β) oracle x a := by
      rcases a with ⟨_ | l, v, res⟩
      · rfl
      · have h0 := hdet 0 (by omega) l rfl
        cases hA : A l with
        | det i => exact nastep_det hA β b v res
        | choose l₁ l₀ => rw [hA] at h0; simp [NIns.targets] at h0
    rw [narun_cons, hstep, List.length_cons, arun_succ]
    refine ih _ T (fun t ht l hl => hdet (t + 1) (by omega) l ?_) (by simp at hσ; omega)
    rwa [arun_succ]

end Semantics

/-! ## Proving nondeterministic machines correct -/

/-- **All branches halt**: every choice word `σ` of length `N` halts the machine from `a`, and
every live configuration along the run satisfies the guard `G`. -/
def NHalts (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (G : AConf m Λ → Prop) (a : AConf m Λ) (N : ℕ) : Prop :=
  ∀ σ : List Bool, σ.length = N → (narun A oracle x σ a).1 = none ∧
    ∀ t < N, (narun A oracle x (σ.take t) a).1 ≠ none → G (narun A oracle x (σ.take t) a)

/-- **Some branch answers `b`**: some choice word of length `N` ends the run from `a` with the
answer `b`. -/
def NAns (A : NARM m d Λ) (oracle : Fin d → List Bool → Bool) (x : List Bool)
    (a : AConf m Λ) (N : ℕ) (b : Bool) : Prop :=
  ∃ σ : List Bool, σ.length = N ∧ (narun A oracle x σ a).2.2 = some b

section Combinators

/-- A prefix of length `s ≥ N` is the prefix of length `N` followed by a prefix of the rest. -/
lemma take_split (σ : List Bool) {N s : ℕ} (h : N ≤ s) :
    σ.take s = σ.take N ++ (σ.drop N).take (s - N) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = N + k := ⟨s - N, by omega⟩
  rw [List.take_add]; simp

variable {A : NARM m d Λ} {oracle : Fin d → List Bool → Bool} {G : AConf m Λ → Prop}

/-- A halted configuration halts on every branch. -/
lemma NHalts.halted (v : Fin m → ℕ) (res : Option Bool) (N : ℕ) :
    NHalts A oracle x G (none, v, res) N :=
  fun σ _ => ⟨by simp, fun t _ h => by simp at h⟩

/-- All-branch halting through a guard is all-branch halting through any weaker guard. -/
lemma NHalts.mono {G' : AConf m Λ → Prop} {a : AConf m Λ} {N : ℕ}
    (h : NHalts A oracle x G a N) (hG : ∀ c, G c → G' c) : NHalts A oracle x G' a N :=
  fun σ hσ => ⟨(h σ hσ).1, fun t ht hl => hG _ ((h σ hσ).2 t ht hl)⟩

/-- **All-branch halting is monotone in the length.**

**Proof sketch.** A word of length `N' ≥ N` is its prefix of length `N`, which halts, followed
by bits that change nothing (`narun_append_of_halted`); guards beyond `N` are at halted
configurations. -/
lemma NHalts.mono_len {a : AConf m Λ} {N N' : ℕ} (h : NHalts A oracle x G a N)
    (hN : N ≤ N') : NHalts A oracle x G a N' := by
  intro σ hσ
  have hlen : (σ.take N).length = N := by simp; omega
  obtain ⟨h1, h2⟩ := h (σ.take N) hlen
  have e : ∀ s, N ≤ s → narun A oracle x (σ.take s) a = narun A oracle x (σ.take N) a := by
    intro s hs
    have : σ.take s = σ.take N ++ (σ.drop N).take (s - N) := by
      exact take_split σ hs
    rw [this, narun_append_of_halted h1]
  refine ⟨?_, fun t ht hl => ?_⟩
  · have := e N' hN; rw [← hσ, List.take_length] at this; rw [this]; exact h1
  · rcases Nat.lt_or_ge t N with htN | htN
    · have := h2 t htN
      rw [List.take_take, min_eq_left htN.le] at this
      exact this hl
    · rw [e t htN] at hl; exact absurd h1 hl

/-- **A deterministic step**: if the guard holds at a live configuration at a deterministic
label, and the machine halts on every branch after the step, it halts on every branch from
the configuration, one step later. -/
lemma NHalts.det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (β : Bool) {v : Fin m → ℕ}
    {res : Option Bool} {N : ℕ} (hG : G (some l, v, res))
    (h : NHalts A oracle x G (astep (A.detPart β) oracle x (some l, v, res)) N) :
    NHalts A oracle x G (some l, v, res) (N + 1) := by
  intro σ hσ
  obtain ⟨b, σ', rfl⟩ : ∃ b σ', σ = b :: σ' := by
    cases σ with
    | nil => simp at hσ
    | cons b σ' => exact ⟨b, σ', rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hσ
  obtain ⟨h1, h2⟩ := h σ' hσ
  refine ⟨by rw [narun_cons, nastep_det hA β]; exact h1, fun t ht hl => ?_⟩
  cases t with
  | zero => exact hG
  | succ t =>
    simp only [List.take_succ_cons, narun_cons, nastep_det hA β] at hl ⊢
    exact h2 t (by omega) hl

/-- **A `choose`**: if the guard holds at a live configuration at a `choose` label, and the
machine halts on every branch from both targets, it halts on every branch from the
configuration, one step later.

**Proof sketch.** A word of length `N + 1` is a bit `b` followed by a word of length `N`; the
first step moves to the target selected by `b`, from which the rest halts with the guard along
the way; the guard at time `0` is the hypothesis. -/
lemma NHalts.choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) {v : Fin m → ℕ}
    {res : Option Bool} {N : ℕ} (hG : G (some l, v, res))
    (h₁ : NHalts A oracle x G (some l₁, v, res) N) (h₀ : NHalts A oracle x G (some l₀, v, res) N) :
    NHalts A oracle x G (some l, v, res) (N + 1) := by
  intro σ hσ
  obtain ⟨b, σ', rfl⟩ : ∃ b σ', σ = b :: σ' := by
    cases σ with
    | nil => simp at hσ
    | cons b σ' => exact ⟨b, σ', rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hσ
  have key : ∀ c : Bool, NHalts A oracle x G (some (if c then l₁ else l₀), v, res) N := by
    intro c; cases c
    · simpa using h₀
    · simpa using h₁
  obtain ⟨h1, h2⟩ := key b σ' hσ
  refine ⟨by rw [narun_cons, nastep_choose hA]; exact h1, fun t ht hl => ?_⟩
  cases t with
  | zero => exact hG
  | succ t =>
    simp only [List.take_succ_cons, narun_cons, nastep_choose hA] at hl ⊢
    exact h2 t (by omega) hl

/-- **A deterministic run**: if the deterministic part runs `T` steps from `a` to `a'` without
meeting a `choose` label, through configurations satisfying the guard, and the machine halts
on every branch from `a'` within `N`, it halts on every branch from `a` within `T + N`.

**Proof sketch.** On the first `T` bits the nondeterministic run is the deterministic one
(`narun_eq_arun`), reaching `a'`; the remaining `N` bits halt from `a'`. Guards before `T`
are those of the deterministic run, later ones those of the run from `a'` (`take_split`). -/
lemma NHalts.run (β : Bool) {a a' : AConf m Λ} {T N : ℕ}
    (he : arun (A.detPart β) oracle x a T = a')
    (hG : ∀ t < T, G (arun (A.detPart β) oracle x a t) ∧
      ∀ l, (arun (A.detPart β) oracle x a t).1 = some l → (A l).targets = none)
    (h : NHalts A oracle x G a' N) : NHalts A oracle x G a (T + N) := by
  intro σ hσ
  have hT : (σ.take T).length = T := by simp; omega
  have e1 : narun A oracle x (σ.take T) a = a' := by
    rw [narun_eq_arun β a T (fun t ht => (hG t ht).2) _ hT.le, hT, he]
  have hd : (σ.drop T).length = N := by simp; omega
  obtain ⟨h1, h2⟩ := h (σ.drop T) hd
  refine ⟨by rw [← List.take_append_drop T σ, narun_append, e1]; exact h1, fun t ht hl => ?_⟩
  rcases Nat.lt_or_ge t T with htT | htT
  · have hlen : (σ.take t).length ≤ T := by simp; omega
    rw [narun_eq_arun β a T (fun t ht => (hG t ht).2) _ hlen] at hl ⊢
    have : (σ.take t).length = t := by simp; omega
    rw [this]; exact (hG t htT).1
  · have e : σ.take t = σ.take T ++ (σ.drop T).take (t - T) := by
      exact take_split σ htT
    rw [e, narun_append, e1] at hl ⊢
    exact h2 (t - T) (by omega) hl

/-- The guard holds at the start of a run halting on every branch, if the start is live. -/
lemma NHalts.guard {l : Λ} {v : Fin m → ℕ} {res : Option Bool} {N : ℕ}
    (h : NHalts A oracle x G (some l, v, res) (N + 1)) : G (some l, v, res) := by
  have := (h (List.replicate (N + 1) false) (by simp)).2 0 (by omega)
  simpa using this

/-- All branches from a deterministic step halt one step earlier from its successor. -/
lemma NHalts.of_det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (β : Bool) {v : Fin m → ℕ}
    {res : Option Bool} {N : ℕ} (h : NHalts A oracle x G (some l, v, res) (N + 1)) :
    NHalts A oracle x G (astep (A.detPart β) oracle x (some l, v, res)) N := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := h (false :: σ) (by simp [hσ])
  refine ⟨by rwa [narun_cons, nastep_det hA β] at h1, fun t ht hl => ?_⟩
  have := h2 (t + 1) (by omega)
  simp only [List.take_succ_cons, narun_cons, nastep_det hA β] at this
  exact this hl

/-- All branches from a `choose` halt one step earlier from either target. -/
lemma NHalts.of_choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) (b : Bool) {v : Fin m → ℕ}
    {res : Option Bool} {N : ℕ} (h : NHalts A oracle x G (some l, v, res) (N + 1)) :
    NHalts A oracle x G (some (if b then l₁ else l₀), v, res) N := by
  intro σ hσ
  obtain ⟨h1, h2⟩ := h (b :: σ) (by simp [hσ])
  refine ⟨by rwa [narun_cons, nastep_choose hA] at h1, fun t ht hl => ?_⟩
  have := h2 (t + 1) (by omega)
  simp only [List.take_succ_cons, narun_cons, nastep_choose hA] at this
  exact this hl

/-- The answers of a halted configuration. -/
lemma nans_halted (v : Fin m → ℕ) (res : Option Bool) (N : ℕ) (b : Bool) :
    NAns A oracle x (none, v, res) N b ↔ res = some b := by
  constructor
  · rintro ⟨σ, -, h⟩; simpa using h
  · intro h; exact ⟨List.replicate N false, by simp, by simpa using h⟩

/-- **The answers after a deterministic step** are those of the next configuration. -/
lemma nans_det {l : Λ} {i : Ins m d Λ} (hA : A l = .det i) (β : Bool) (v : Fin m → ℕ)
    (res : Option Bool) (N : ℕ) (b : Bool) :
    NAns A oracle x (some l, v, res) (N + 1) b ↔
      NAns A oracle x (astep (A.detPart β) oracle x (some l, v, res)) N b := by
  constructor
  · rintro ⟨σ, hσ, h⟩
    obtain ⟨c, σ', rfl⟩ : ∃ c σ', σ = c :: σ' := by
      cases σ with
      | nil => simp at hσ
      | cons c σ' => exact ⟨c, σ', rfl⟩
    refine ⟨σ', by simpa using hσ, ?_⟩
    rwa [narun_cons, nastep_det hA β] at h
  · rintro ⟨σ, hσ, h⟩
    exact ⟨false :: σ, by simp [hσ], by rwa [narun_cons, nastep_det hA β]⟩

/-- **The answers after a `choose`** are those of either target. -/
lemma nans_choose {l l₁ l₀ : Λ} (hA : A l = .choose l₁ l₀) (v : Fin m → ℕ)
    (res : Option Bool) (N : ℕ) (b : Bool) :
    NAns A oracle x (some l, v, res) (N + 1) b ↔
      NAns A oracle x (some l₁, v, res) N b ∨ NAns A oracle x (some l₀, v, res) N b := by
  constructor
  · rintro ⟨σ, hσ, h⟩
    obtain ⟨c, σ', rfl⟩ : ∃ c σ', σ = c :: σ' := by
      cases σ with
      | nil => simp at hσ
      | cons c σ' => exact ⟨c, σ', rfl⟩
    rw [narun_cons, nastep_choose hA] at h
    cases c
    · exact Or.inr ⟨σ', by simpa using hσ, by simpa using h⟩
    · exact Or.inl ⟨σ', by simpa using hσ, by simpa using h⟩
  · rintro (⟨σ, hσ, h⟩ | ⟨σ, hσ, h⟩)
    · exact ⟨true :: σ, by simp [hσ], by rw [narun_cons, nastep_choose hA]; simpa using h⟩
    · exact ⟨false :: σ, by simp [hσ], by rw [narun_cons, nastep_choose hA]; simpa using h⟩

/-- **The answers after a deterministic run** (without `choose` labels) are those of its end. -/
lemma nans_run (β : Bool) {a a' : AConf m Λ} {T : ℕ}
    (he : arun (A.detPart β) oracle x a T = a')
    (hdet : ∀ t < T, ∀ l, (arun (A.detPart β) oracle x a t).1 = some l → (A l).targets = none)
    (N : ℕ) (b : Bool) : NAns A oracle x a (T + N) b ↔ NAns A oracle x a' N b := by
  have key : ∀ σ τ : List Bool, σ.length = T →
      narun A oracle x (σ ++ τ) a = narun A oracle x τ a' := by
    intro σ τ hσ
    rw [narun_append, narun_eq_arun β a T hdet σ hσ.le, hσ, he]
  constructor
  · rintro ⟨σ, hσ, h⟩
    refine ⟨σ.drop T, by simp; omega, ?_⟩
    rwa [← List.take_append_drop T σ, key _ _ (by simp; omega)] at h
  · rintro ⟨τ, hτ, h⟩
    exact ⟨List.replicate T false ++ τ, by simp [hτ], by rwa [key _ _ (by simp)]⟩

/-- **Answers are stable beyond all-branch halting**: if every branch halts within `N`, the
answers of branches of any length `N' ≥ N` are those of length `N`. -/
lemma nans_mono_len {a : AConf m Λ} {N N' : ℕ} (h : NHalts A oracle x G a N) (hN : N ≤ N')
    (b : Bool) : NAns A oracle x a N' b ↔ NAns A oracle x a N b := by
  constructor
  · rintro ⟨σ, hσ, hb⟩
    have hlen : (σ.take N).length = N := by simp; omega
    refine ⟨σ.take N, hlen, ?_⟩
    rwa [← List.take_append_drop N σ, narun_append_of_halted (h _ hlen).1] at hb
  · rintro ⟨σ, hσ, hb⟩
    refine ⟨σ ++ List.replicate (N' - N) false, by simp; omega, ?_⟩
    rwa [narun_append_of_halted (h σ hσ).1]

end Combinators

end Complexity.LogProg
