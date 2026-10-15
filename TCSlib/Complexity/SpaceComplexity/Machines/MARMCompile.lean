/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.MARM
import TCSlib.Complexity.SpaceComplexity.Machines.NARMCompile

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compiling memory register machines

The compiled machine of a memory register machine `A` (`Complexity.LogProg.mcompileTM`) has
the work tapes of the compiled deterministic part `A.detPart false` (registers and decider
block) and one more tape, the memory. Away from the start states of memory instructions it
makes the step of the compiled deterministic part, leaving the memory tape alone
(`Complexity.LogProg.liftAct`); at those start states it makes one step on the memory tape.
The memory tape holds `1` as the symbol `true` and `0` as a blank, so the only symbol ever
written on it is `true`.

As for nondeterministic machines (`TCSlib.Complexity.SpaceComplexity.Machines.NARMCompile`),
no instruction-level simulation is redone: at a memory start state the compiled deterministic
part halts at once, so its runs that end live (or with the other answer) avoid those states,
and the compiled memory machine follows them (`Complexity.LogProg.mrunFrom_eq`).

This is infrastructure for [AB09, §4.1.1], not itself a result of the book.

## Main definitions

* `Complexity.LogProg.liftAct`, `Complexity.LogProg.memCfg` — an extra, idle tape.
* `Complexity.LogProg.mcompileTM`, `Complexity.LogProg.mcompileFinTM` — the compiled machine.
* `Complexity.LogProg.mseam` — the compiled configuration of a memory machine configuration.
* `Complexity.LogProg.MBox` — head ranges of registers, deciders and memory.

## Main results

* `Complexity.LogProg.mdet_live`, `Complexity.LogProg.mdet_halt` — the register steps.
* `Complexity.LogProg.mmem_step` — a memory step is one compiled step.
* `Complexity.LogProg.mcompileTM_init` — the initial configuration.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## An extra tape -/

section Lift

variable {K : ℕ} {St : Type} {x : List Bool}

/-- The memory tape of memory bits: `true` at the `1`s, blank at the `0`s. -/
def memTape (M : ℤ → Bool) : ℤ → Option Bool := fun z => if M z then some true else none

/-- An action with one more work tape, left alone. -/
def liftAct (a : Action K Bool St) : Action (K + 1) Bool St :=
  ⟨a.inputTape, Fin.snoc (α := fun _ => Option (Option Bool) × SignType) a.workTapes (none, 0),
    a.output, a.state⟩

/-- A configuration with one more work tape holding `M`, its head at `p`. -/
def memCfg (c : Cfg K Bool St x) (M : ℤ → Option Bool) (p : ℤ) : Cfg (K + 1) Bool St x :=
  ⟨c.state, c.inputPos, Fin.snoc (α := fun _ => ℤ → Option Bool) c.workTapes M,
    Fin.snoc (α := fun _ => ℤ) c.workTapePos p, c.output⟩

/-- The old tapes read as before. -/
@[simp] lemma memCfg_symbols_castSucc (c : Cfg K Bool St x) (M : ℤ → Option Bool) (p : ℤ)
    (i : Fin K) : (memCfg c M p).workTapeSymbols i.castSucc = c.workTapeSymbols i := by
  simp [memCfg, Cfg.workTapeSymbols]

/-- The extra tape reads its cell under the head. -/
@[simp] lemma memCfg_symbols_last (c : Cfg K Bool St x) (M : ℤ → Option Bool) (p : ℤ) :
    (memCfg c M p).workTapeSymbols (Fin.last K) = M p := by
  simp [memCfg, Cfg.workTapeSymbols]

/-- A lifted action acts on the old tapes and leaves the extra tape alone. -/
lemma liftAct_apply (a : Action K Bool St) (c : Cfg K Bool St x) (M : ℤ → Option Bool) (p : ℤ) :
    (liftAct a).apply (memCfg c M p) = memCfg (a.apply c) M p := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Action.apply, liftAct, memCfg]
    · simp only [Action.apply, liftAct, memCfg, Fin.snoc_castSucc]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Action.apply, liftAct, memCfg]
    · simp [Action.apply, liftAct, memCfg]

end Lift

/-! ## The compiled machine -/

section Construction

variable {m d kD : ℕ} {Λ SD : Type}

/-- The memory instruction whose fragment starts at a compiled state (`none` elsewhere). -/
def mop (A : MARM m d Λ) : CSt (Λ × Ph) SD m → Option (MIns m d Λ)
  | .prog (l, ph) => if ph = .start ∧ (A l).isMem = true then some (A l) else none
  | _ => none

/-- A compiled state with a memory instruction is the start state of its fragment. -/
lemma mop_spec {A : MARM m d Λ} {q : CSt (Λ × Ph) SD m} {i : MIns m d Λ}
    (h : mop A q = some i) : ∃ l, q = .prog (l, .start) ∧ A l = i ∧ i.isMem = true := by
  match q, h with
  | .prog (l, ph), h =>
    simp only [mop] at h
    split_ifs at h with hph
    · obtain ⟨rfl, hm⟩ := hph
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨l, rfl, rfl, hm⟩

/-- The one-step action of a memory instruction, reading the memory symbol `r`. -/
def memAct {K : ℕ} (i : MIns m d Λ) (r : Option Bool) : Action (K + 1) Bool (CSt (Λ × Ph) SD m) :=
  match i with
  | .det _ => ⟨0, fun _ => (none, 0), none, none⟩
  | .mread l₁ l₀ =>
    ⟨0, fun _ => (none, 0), none, some (.prog ((if r = some true then l₁ else l₀), .start))⟩
  | .mset l =>
    ⟨0, Fin.snoc (α := fun _ => Option (Option Bool) × SignType) (fun _ => (none, 0))
      (some (some true), 0), none, some (.prog (l, .start))⟩
  | .mleft l =>
    ⟨0, Fin.snoc (α := fun _ => Option (Option Bool) × SignType) (fun _ => (none, 0)) (none, -1),
      none, some (.prog (l, .start))⟩
  | .mright l =>
    ⟨0, Fin.snoc (α := fun _ => Option (Option Bool) × SignType) (fun _ => (none, 0)) (none, 1),
      none, some (.prog (l, .start))⟩

/-- **The compiled memory machine** of a memory register machine `A` with start label `l₀`,
calling the deciders `D` from the start states `q0 j`: at the start state of a memory
instruction one step on the memory tape (the last work tape), everywhere else the step of the
compiled deterministic part with the memory tape idle. -/
def mcompileTM (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    MultiTapeTM (m + kD + 1) Bool (CSt (Λ × Ph) SD m) where
  q₀ := .prog (l₀, .start)
  tr q a w :=
    match mop A q with
    | some i => memAct i (w (Fin.last _))
    | none => liftAct (ctr (armProg (A.detPart false) l₀) D q0 q a (fun i => w i.castSucc))

/-- The compiled memory machine as a bundled finite machine. -/
def mcompileFinTM [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) : FinTM Bool where
  k := m + kD + 1
  State := CSt (Λ × Ph) SD m
  tm := mcompileTM A l₀ D q0

/-- The compiled deterministic part answering `β` at the memory labels. -/
abbrev detM (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (β : Bool) : MultiTapeTM (m + kD) Bool (CSt (Λ × Ph) SD m) :=
  compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0

/-- The call nodes of the compiled deterministic parts do not depend on the answer at the
memory labels. -/
lemma armProg_mdetPart_call (A : MARM m d Λ) (l₀ : Λ) (β β' : Bool) :
    (armProg (A.detPart β) l₀).call = (armProg (A.detPart β') l₀).call := by
  funext q
  obtain ⟨l, ph⟩ := q
  show insCall (A.detPart β l) ph = insCall (A.detPart β' l) ph
  cases hA : A l with
  | det i => rw [MARM.detPart_det hA, MARM.detPart_det hA]
  | _ =>
    rw [MARM.detPart_mem (by simp [hA, MIns.isMem]), MARM.detPart_mem (by simp [hA, MIns.isMem])]
    rfl

/-- Away from the memory start states, the compiled deterministic parts agree. -/
lemma detM_tr (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    {q : CSt (Λ × Ph) SD m} (hq : mop A q = none) (β : Bool) :
    (detM A l₀ D q0 β).tr q = (detM A l₀ D q0 false).tr q := by
  funext a w
  simp only [detM, compileTM]
  rw [ctr_congr D q0 q (armProg_mdetPart_call A l₀ β false) ?_]
  rintro ⟨l, ph⟩ rfl
  funext a' w'
  show insTr (A.detPart β l) l ph a' w' = insTr (A.detPart false l) l ph a' w'
  cases hA : A l with
  | det i => rw [MARM.detPart_det hA, MARM.detPart_det hA]
  | _ =>
    have hph : ph ≠ .start := by
      rintro rfl; simp [mop, hA, MIns.isMem] at hq
    rw [MARM.detPart_mem (by simp [hA, MIns.isMem]), MARM.detPart_mem (by simp [hA, MIns.isMem])]
    cases ph <;> first | exact absurd rfl hph | rfl

/-- **Away from the memory start states, the compiled memory machine makes the step of the
compiled deterministic part** (for either answer `β`), its memory tape idle. -/
lemma mcompileTM_step (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (β : Bool) {x : List Bool} (c : Cfg (m + kD) Bool (CSt (Λ × Ph) SD m) x)
    (hc : ∀ q, c.state = some q → mop A q = none) (M : ℤ → Option Bool) (p : ℤ) :
    (mcompileTM A l₀ D q0).step (memCfg c M p) = memCfg ((detM A l₀ D q0 β).step c) M p := by
  unfold MultiTapeTM.step
  cases hs : c.state with
  | none => simp [memCfg, hs]
  | some q =>
    have hq := hc q hs
    have hst : (memCfg c M p).state = some q := by simp [memCfg, hs]
    rw [hst]
    simp only
    rw [detM_tr A l₀ D q0 hq β]
    have hsym : (fun i => (memCfg c M p).workTapeSymbols i.castSucc) = c.workTapeSymbols := by
      funext i; simp
    have hin : (memCfg c M p).inputSymbol = c.inputSymbol := rfl
    simp only [mcompileTM, hq, hsym, hin]
    exact liftAct_apply _ c M p

/-- **The compiled memory machine follows the compiled deterministic part** along its runs
that avoid the memory start states, its memory tape idle.

**Proof sketch.** Induction on the time, by `mcompileTM_step`. -/
lemma mrunFrom_eq (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (β : Bool) {x : List Bool} (c : Cfg (m + kD) Bool (CSt (Λ × Ph) SD m) x) (M : ℤ → Option Bool)
    (p : ℤ) (T : ℕ)
    (hX : ∀ t < T, ∀ q, ((detM A l₀ D q0 β).runFrom c t).state = some q → mop A q = none) :
    ∀ t ≤ T, (mcompileTM A l₀ D q0).runFrom (memCfg c M p) t =
      memCfg ((detM A l₀ D q0 β).runFrom c t) M p := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    exact mcompileTM_step A l₀ D q0 β _ (hX t (by omega)) M p

/-- **At a memory start state the compiled deterministic part halts at once, writing `β`.** -/
lemma detM_step_mem (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (β : Bool) {x : List Bool} (c : Cfg (m + kD) Bool (CSt (Λ × Ph) SD m) x)
    (q : CSt (Λ × Ph) SD m) (hc : c.state = some q) (hq : mop A q ≠ none) :
    ((detM A l₀ D q0 β).step c).state = none ∧
      ((detM A l₀ D q0 β).step c).output = c.output ++ [β] := by
  obtain ⟨i, hq'⟩ := Option.ne_none_iff_exists'.mp hq
  obtain ⟨l, rfl, hA, hm⟩ := mop_spec hq'
  have hret : A.detPart β l = .ret β := MARM.detPart_mem (by rw [hA]; exact hm) β
  have hcall : (armProg (A.detPart β) l₀).call (l, .start) = none := by
    show insCall (A.detPart β l) .start = none
    rw [hret]; rfl
  have htr : ∀ a w, (armProg (A.detPart β) l₀).tm.tr (l, .start) a w = retAct β := by
    intro a w
    show insTr (A.detPart β l) l .start a w = retAct β
    rw [hret]; rfl
  unfold MultiTapeTM.step
  rw [hc]
  simp only [detM, compileTM, ctr, hcall, htr, retAct, Action.apply]
  exact ⟨rfl, by simp⟩

/-- The deterministic parts have the same preconditions. -/
lemma pre_mdetPart (A : MARM m d Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B : ℕ) {x : List Bool} (β β' : Bool)
    (a : AConf m Λ) :
    Pre (A.detPart β) oracle D q0 B x a ↔ Pre (A.detPart β') oracle D q0 B x a := by
  rcases a with ⟨_ | l, v, res⟩
  · exact Iff.rfl
  · cases hA : A l with
    | det i => simp only [Pre, MARM.detPart_det hA]
    | _ =>
      simp only [Pre, MARM.detPart_mem (A := A) (l := l) (by simp [hA, MIns.isMem])]

/-- At a register label the deterministic parts make the same step. -/
lemma astep_mdetPart {A : MARM m d Λ} {l : Λ} {i : Ins m d Λ} (hA : A l = .det i)
    (oracle : Fin d → List Bool → Bool) {x : List Bool} (β β' : Bool) (v : Fin m → ℕ)
    (res : Option Bool) :
    astep (A.detPart β) oracle x (some l, v, res) =
      astep (A.detPart β') oracle x (some l, v, res) := by
  simp only [astep, MARM.detPart_det hA]

/-- The compiled configuration of a memory machine configuration: the compiled program
configuration of the registers, and the memory tape. -/
def mseam (x : List Bool) (l : Λ) (v : Fin m → ℕ) (M : ℤ → Bool) (p : ℤ) (out : List Bool) :
    Cfg (m + kD + 1) Bool (CSt (Λ × Ph) SD m) x :=
  memCfg (seam (kD := kD) (SD := SD) (aseam x l v out)) (memTape M) p

/-- The initial configuration of the compiled memory machine is the compiled configuration of
the start label, all registers `0`, the memory blank with its head at `0`. -/
lemma mcompileTM_init (A : MARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (x : List Bool) :
    (mcompileTM A l₀ D q0).initCfg x = mseam x l₀ (fun _ => 0) (fun _ => false) 0 [] := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [mseam, memCfg, memTape]
    · simp only [mseam, memCfg, Fin.snoc_castSucc]
      refine Fin.addCases (fun r => ?_) (fun k => ?_) j <;>
        simp [seam, aseam, Nat.zero_bits]
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [mseam, memCfg]
    · simp only [mseam, memCfg, Fin.snoc_castSucc]
      refine Fin.addCases (fun r => ?_) (fun k => ?_) j <;> simp [seam, aseam]

end Construction

/-! ## Simulating the steps -/

section Steps

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- A compiled memory configuration with register heads in `[-1, W]`, decider heads in
`[-B, B]` and the memory head in `[-P, P]`. -/
def MBox {St : Type} (W B P : ℕ) (C : Cfg (m + kD + 1) Bool St x) : Prop :=
  (∀ r : Fin m, (-1 : ℤ) ≤ C.workTapePos (Fin.castAdd kD r).castSucc ∧
    C.workTapePos (Fin.castAdd kD r).castSucc ≤ W) ∧
  (∀ i : Fin kD, |C.workTapePos (Fin.natAdd m i).castSucc| ≤ B) ∧
  |C.workTapePos (Fin.last _)| ≤ P

/-- The compiled configuration of a memory machine configuration is in the box. -/
lemma mbox_mseam (W B P : ℕ) (l : Λ) (v : Fin m → ℕ) (M : ℤ → Bool) (p : ℤ) (out : List Bool)
    (hp : |p| ≤ P) :
    MBox (kD := kD) (St := CSt (Λ × Ph) SD m) W B P (mseam x l v M p out) :=
  ⟨fun r => by simp only [mseam, memCfg, Fin.snoc_castSucc]; simp [seam, aseam],
    fun i => by simp only [mseam, memCfg, Fin.snoc_castSucc]; simp [seam],
    by simpa [mseam, memCfg] using hp⟩

/-- A lifted configuration is in the box when the original one has its register and decider
heads in range and the memory head is in range. -/
lemma mbox_memCfg {St : Type} (W B P : ℕ) (c : Cfg (m + kD) Bool St x) (M : ℤ → Option Bool)
    (p : ℤ) (h1 : ∀ r : Fin m, (-1 : ℤ) ≤ c.workTapePos (Fin.castAdd kD r) ∧
      c.workTapePos (Fin.castAdd kD r) ≤ W)
    (h2 : ∀ i : Fin kD, |c.workTapePos (Fin.natAdd m i)| ≤ B) (hp : |p| ≤ P) :
    MBox W B P (memCfg c M p) :=
  ⟨fun r => by simp only [memCfg, Fin.snoc_castSucc]; exact h1 r,
    fun i => by simp only [memCfg, Fin.snoc_castSucc]; exact h2 i,
    by simpa [memCfg] using hp⟩

/-- **A live register step.** If, at a register label, the deterministic part steps from
`(l, v)` to the live `(l', v')`, with the preconditions and register widths of `arm_step`,
then the compiled memory machine goes from the compiled configuration of `(l, v)` to that of
`(l', v')`, the memory unchanged, in the box.

**Proof sketch.** `arm_step` and `compile_correct_from` give a run of the compiled
deterministic part reaching the seam of `(l', v')`, in range. It ends live, so it avoids the
memory start states (`avoid_of_live`, `detM_step_mem`), and the compiled memory machine
follows it (`mrunFrom_eq`). -/
theorem mdet_live (A : MARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W P : ℕ) (l l' : Λ) (v v' : Fin m → ℕ)
    (M : ℤ → Bool) (p : ℤ) (out : List Bool)
    (hs : astep (A.detPart false) oracle x (some l, v, none) = (some l', v', none))
    (hp : Pre (A.detPart false) oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) (hP : |p| ≤ P) :
    ∃ S, (mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) S = mseam x l' v' M p out ∧
      ∀ t ≤ S, MBox W B P ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) t) := by
  obtain ⟨T, e, hinv⟩ := arm_step (A.detPart false) l₀ oracle D q0 B W l l' v v' out hs hp hw
  obtain ⟨S, hS, hb⟩ := compile_correct_from (armProg (A.detPart false) l₀) (l₀, .start) D q0
    oracle (fun _ => -1) (fun _ => (W : ℤ)) B (aseam x l v out) T
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hinv t h).1 r
      · obtain rfl : t = T := by omega
        rw [e]; simp [aseam])
    (fun t ht => (hinv t ht).2)
  have hX := avoid_of_live (detM A l₀ D q0 false) (fun q => mop A q ≠ none)
    (fun c q hc hq => (detM_step_mem A l₀ D q0 false c q hc hq).1)
    (seam (aseam x l v out)) S (by rw [hS, e]; simp [seam, aseam])
  have hag := mrunFrom_eq A l₀ D q0 false (seam (aseam x l v out)) (memTape M) p S
    (fun t ht q hq => not_not.mp (hX t ht q hq))
  refine ⟨S, ?_, fun t ht => ?_⟩
  · rw [mseam, hag S le_rfl, hS, e]; rfl
  · rw [mseam, hag t ht]
    exact mbox_memCfg W B P _ _ p (hb t ht).1 (hb t ht).2 hP

/-- **A halting register step.** If, at a register label, the deterministic part halts from
`(l, v)` with answer `b₀`, with the preconditions and register widths of `arm_run`, then the
compiled memory machine halts from the compiled configuration of `(l, v)` with output
`out ++ [b₀]`, in the box.

**Proof sketch.** As `mdet_live`, with `arm_run` (one step) for the deterministic part
answering `!b₀` at the memory labels: its run ends with answer `b₀ ≠ !b₀`, so it avoids the
memory start states (`avoid_of_halt`). -/
theorem mdet_halt (A : MARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W P : ℕ) (l : Λ) {i : Ins m d Λ}
    (hA : A l = .det i) (v : Fin m → ℕ) (M : ℤ → Bool) (p : ℤ) (out : List Bool) (b₀ : Bool)
    (hs : astep (A.detPart false) oracle x (some l, v, none) = (none, v, some b₀))
    (hp : Pre (A.detPart false) oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) (hP : |p| ≤ P) :
    ∃ S, ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) S).state = none ∧
      ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) S).output = out ++ [b₀] ∧
      ∀ t ≤ S, MBox W B P ((mcompileTM A l₀ D q0).runFrom (mseam x l v M p out) t) := by
  have hs' : astep (A.detPart (!b₀)) oracle x (some l, v, none) = (none, v, some b₀) := by
    rw [astep_mdetPart hA oracle (!b₀) false]; exact hs
  obtain ⟨T, e1, e2, e3, hinv⟩ := arm_run (x := x) (A.detPart (!b₀)) l₀ oracle D q0 B W 1 l v out
    b₀ (by simp [arun, hs']) (by simp [arun, hs'])
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      exact ⟨(pre_mdetPart A oracle D q0 B false (!b₀) _).1 hp, hw⟩)
  obtain ⟨S, hS, hb⟩ := compile_correct_from (armProg (A.detPart (!b₀)) l₀) (l₀, .start) D q0
    oracle (fun _ => -1) (fun _ => (W : ℤ)) B (aseam x l v out) T
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hinv t h).1 r
      · obtain rfl : t = T := by omega
        exact e3 r)
    (fun t ht => (hinv t ht).2)
  have hX := avoid_of_halt (detM A l₀ D q0 (!b₀)) (fun q => mop A q ≠ none) (!b₀)
    (fun c q hc hq => detM_step_mem A l₀ D q0 (!b₀) c q hc hq)
    (seam (aseam x l v out)) S b₀ (by rw [hS]; exact e2) (by cases b₀ <;> simp)
  have hag := mrunFrom_eq A l₀ D q0 (!b₀) (seam (aseam x l v out)) (memTape M) p S
    (fun t ht q hq => not_not.mp (hX t ht q hq))
  refine ⟨S, ?_, ?_, fun t ht => ?_⟩
  · rw [mseam, hag S le_rfl, hS]
    exact seam_state_none (kD := kD) (SD := SD) _ e1
  · rw [mseam, hag S le_rfl, hS]
    exact e2
  · rw [mseam, hag t ht]
    exact mbox_memCfg W B P _ _ p (hb t ht).1 (hb t ht).2 hP

/-- **A memory step is one compiled step**: at a memory label, the compiled memory machine
goes in one step from the compiled configuration of a configuration to that of its successor.

**Proof sketch.** At the start state of a memory instruction the compiled transition is
`memAct`: it reads the memory cell under the head, moves only the memory head or writes `true`
under it, and goes to the target label. Compare the components of the two configurations
(`Fin.lastCases` on the tapes: the old tapes are untouched). -/
lemma mmem_step (A : MARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) {l : Λ} (hA : (A l).isMem = true)
    (v : Fin m → ℕ) (M : ℤ → Bool) (p : ℤ) (out : List Bool) :
    ∃ l' M' p', mstep A oracle x ((some l, v, none), (M, p)) = ((some l', v, none), (M', p')) ∧
      (mcompileTM A l₀ D q0).step (mseam x l v M p out) = mseam x l' v M' p' out := by
  have hst : (mseam (kD := kD) (SD := SD) x l v M p out).state = some (.prog (l, .start)) := rfl
  have hmop : mop (SD := SD) A (.prog (l, .start)) = some (A l) := by simp [mop, hA]
  have hlast : (mseam (kD := kD) (SD := SD) x l v M p out).workTapeSymbols (Fin.last _) =
      memTape M p := by simp [mseam]
  have key : ∀ (l' : Λ) (M' : ℤ → Bool) (p' : ℤ)
      (a : Action (m + kD + 1) Bool (CSt (Λ × Ph) SD m)),
      a.inputTape = 0 → a.output = none → a.state = some (.prog (l', .start)) →
      (∀ j : Fin (m + kD), a.workTapes j.castSucc = (none, 0)) →
      ((a.workTapes (Fin.last _)).1 = none ∧ M' = M ∨
        (a.workTapes (Fin.last _)).1 = some (some true) ∧ M' = Function.update M p true) →
      p + ((a.workTapes (Fin.last _)).2 : ℤ) = p' →
      a.apply (mseam x l v M p out) = mseam x l' v M' p' out := by
    intro l' M' p' a h1 h2 h3 h4 h5 h6
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_
    · simp [Action.apply, h3, mseam, memCfg, seam, aseam]
    · simp [Action.apply, h1, mseam, memCfg, seam, aseam]
    · funext i z
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Action.apply, mseam, memCfg, Fin.snoc_last]
        rcases h5 with ⟨hw, rfl⟩ | ⟨hw, rfl⟩
        · simp only [hw]
        · simp only [hw]
          by_cases hz : z = p
          · subst hz; simp [memTape]
          · simp [memTape, Function.update_of_ne hz]
      · simp only [Action.apply, h4 j, mseam, memCfg, Fin.snoc_castSucc]; rfl
    · funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [Action.apply, mseam, memCfg, Fin.snoc_last]
        exact h6
      · simp only [Action.apply, h4 j, mseam, memCfg, Fin.snoc_castSucc]; simp; rfl
    · simp [Action.apply, h2, mseam, memCfg, seam, aseam]
  unfold MultiTapeTM.step
  rw [hst]
  simp only [mcompileTM, hmop, hlast]
  cases hA' : A l with
  | det i => rw [hA'] at hA; simp [MIns.isMem] at hA
  | mread l₁ l₀' =>
    refine ⟨if M p then l₁ else l₀', M, p, by simp [mstep, hA'], key _ M p _ rfl rfl ?_
      (fun j => rfl) (Or.inl ⟨rfl, rfl⟩) (by simp [memAct])⟩
    by_cases hM : M p <;> simp [memAct, memTape, hM]
  | mset l' =>
    refine ⟨l', Function.update M p true, p, by simp [mstep, hA'], key _ _ p _ rfl rfl rfl
      (fun j => by simp [memAct]) (Or.inr ⟨by simp [memAct], rfl⟩) (by simp [memAct])⟩
  | mleft l' =>
    refine ⟨l', M, p - 1, by simp [mstep, hA'], key _ M _ _ rfl rfl rfl
      (fun j => by simp [memAct]) (Or.inl ⟨by simp [memAct], rfl⟩) (by simp [memAct]; ring)⟩
  | mright l' =>
    refine ⟨l', M, p + 1, by simp [mstep, hA'], key _ M _ _ rfl rfl rfl
      (fun j => by simp [memAct]) (Or.inl ⟨by simp [memAct], rfl⟩) (by simp [memAct])⟩

end Steps

end Complexity.LogProg
