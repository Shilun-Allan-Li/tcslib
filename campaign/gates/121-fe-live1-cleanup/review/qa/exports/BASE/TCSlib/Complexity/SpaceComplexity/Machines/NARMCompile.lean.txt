/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Machines.NARM
import TCSlib.Complexity.TuringMachine.NondeterministicSpace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Compiling nondeterministic abstract register machines

The compiled nondeterministic machine of a nondeterministic abstract register machine `A`
(`Complexity.LogProg.ncompileTM`) is a `Turing.NDTM` whose two transition functions agree with
the compiled deterministic machine `M_β` of `A.detPart β` (the deterministic instructions, with
`ret β` at the `choose` labels) everywhere except at the start states of the `choose`
fragments, where the choice bit selects the target label by a pure control move.

At a `choose` start state `M_β` halts at once, writing `β`. So a run of `M_β` that ends live,
or halted with an answer other than `β`, never passes through a `choose` start state before
its end, and every branch of the nondeterministic machine follows it
(`Complexity.LogProg.ndtm_runWith_eq_runFrom`, `avoid_of_live`, `avoid_of_halt`). Choosing
`β` opposite to the answer of a halting deterministic step, no instruction-level simulation
has to be redone for `choose`: each deterministic abstract step is simulated by
`Complexity.LogProg.arm_step` / `arm_run` and `Complexity.LogProg.compile_correct_from`
(`Complexity.LogProg.ndet_live`, `Complexity.LogProg.ndet_halt`), and each `choose` is one
control step (`Complexity.LogProg.ncompileTM_stepWith_choose`).

This is infrastructure for [AB09, §4.1–4.3], not itself a result of the book.

## Main definitions

* `Complexity.LogProg.ncompileTM`, `Complexity.LogProg.ncompileFinNDTM` — the compiled
  nondeterministic machine.
* `Complexity.LogProg.NBox` — register heads in `[-1, W]`, decider heads in `[-B, B]`.

## Main results

* `Complexity.LogProg.ndtm_runWith_eq_runFrom` — a nondeterministic machine agreeing with a
  deterministic one off a set of states follows its runs that avoid the set.
* `Complexity.LogProg.ndet_live`, `Complexity.LogProg.ndet_halt` — the deterministic abstract
  steps, on every branch.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.1.2, §4.1.)
-/

namespace Complexity.LogProg

open Turing

/-! ## Nondeterministic machines following deterministic ones -/

section Generic

variable {K : ℕ} {Sym St : Type} {input : List Sym}

/-- **A nondeterministic machine follows a deterministic one off a set of states.** If both
transition functions of `N` agree with that of `M` at the states outside `X`, and the run of
`M` from `c` does not visit `X` before time `T`, then every choice word of length at most `T`
drives `N` along `M`'s run.

**Proof sketch.** Induction on the word: at a halted configuration both machines stay; at a
live one outside `X` the two steps apply the same action. -/
theorem ndtm_runWith_eq_runFrom (N : NDTM K Sym St) (M : MultiTapeTM K Sym St)
    (X : St → Prop) (hNM : ∀ b q, ¬ X q → N.tr b q = M.tr q) (c : Cfg K Sym St input) (T : ℕ)
    (hX : ∀ t < T, ∀ q, (M.runFrom c t).state = some q → ¬ X q)
    (w : List Bool) (hw : w.length ≤ T) : N.runWith w c = M.runFrom c w.length := by
  induction w generalizing c T with
  | nil => rfl
  | cons b w ih =>
    obtain ⟨T, rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by simp at hw; omega⟩
    have hstep : N.stepWith b c = M.step c := by
      cases hc : c.state with
      | none => rw [NDTM.stepWith_of_halt hc, MultiTapeTM.step_of_halt hc]
      | some q =>
        have hq := hX 0 (by omega) q (by simpa using hc)
        simp only [NDTM.stepWith, MultiTapeTM.step, hc, hNM b q hq]
    rw [NDTM.runWith_cons, hstep, List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    exact ih _ T (fun t ht q hq => hX (t + 1) (by omega) q
      (by rwa [MultiTapeTM.runFrom_succ_eq_step])) (by simp at hw; omega)

/-- If `M` halts at once at the states of `X`, a run of `M` ending live does not visit `X`
before its end. -/
lemma avoid_of_live (M : MultiTapeTM K Sym St) (X : St → Prop)
    (hX : ∀ (c : Cfg K Sym St input) q, c.state = some q → X q → (M.step c).state = none)
    (c : Cfg K Sym St input) (T : ℕ) (hT : (M.runFrom c T).state ≠ none) :
    ∀ t < T, ∀ q, (M.runFrom c t).state = some q → ¬ X q := by
  intro t ht q hq hx
  have h1 : (M.runFrom c (t + 1)).state = none := by
    rw [MultiTapeTM.runFrom_succ_eq_step']; exact hX _ q hq hx
  apply hT
  rw [show T = (t + 1) + (T - (t + 1)) by omega, MultiTapeTM.runFrom_add,
    MultiTapeTM.runFrom_of_halt _ h1]
  exact h1

/-- The output of a run extends the starting output. -/
lemma runFrom_output_extends (M : MultiTapeTM K Sym St) (c : Cfg K Sym St input) (t : ℕ) :
    ∃ u, (M.runFrom c t).output = c.output ++ u := by
  induction t with
  | zero => exact ⟨[], by simp⟩
  | succ t ih =>
    obtain ⟨u, hu⟩ := ih
    refine ⟨u ++ (M.outputSymbol (M.runFrom c t)).toList, ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output, hu, List.append_assoc]

/-- If `M` halts at once at the states of `X`, writing `β`, a run of `M` ending with exactly
one more symbol `b ≠ β` does not visit `X` before its end.

**Proof sketch.** A visit at time `t < T` halts the run at `t + 1` with output `o ++ [β]`,
where `o` extends the starting output `o₀` (`runFrom_output_extends`); this is the final
output `o₀ ++ [b]`, so `o = o₀` and `β = b`. -/
lemma avoid_of_halt (M : MultiTapeTM K Sym St) (X : St → Prop) (β : Sym)
    (hX : ∀ (c : Cfg K Sym St input) q, c.state = some q → X q →
      (M.step c).state = none ∧ (M.step c).output = c.output ++ [β])
    (c : Cfg K Sym St input) (T : ℕ) (b : Sym) (hT : (M.runFrom c T).output = c.output ++ [b])
    (hb : b ≠ β) : ∀ t < T, ∀ q, (M.runFrom c t).state = some q → ¬ X q := by
  intro t ht q hq hx
  obtain ⟨h1, h2⟩ := hX _ q hq hx
  rw [← MultiTapeTM.runFrom_succ_eq_step'] at h1 h2
  have e : M.runFrom c T = M.runFrom c (t + 1) := by
    rw [show T = (t + 1) + (T - (t + 1)) by omega, MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_of_halt _ h1]
  obtain ⟨u, hu⟩ := runFrom_output_extends M c t
  rw [e, h2, hu, List.append_assoc] at hT
  have hu' := List.append_cancel_left hT
  rcases u with _ | ⟨y, u⟩
  · simp only [List.nil_append, List.cons.injEq, and_true] at hu'
    exact hb hu'.symm
  · simp at hu'

/-- The space of a branch is bounded by the sizes of ranges containing every head after every
prefix of the choice word. -/
lemma spaceUsedWith_le_of_ranges (N : NDTM K Sym St) (w : List Bool) (c : Cfg K Sym St input)
    (lo hi : Fin K → ℤ)
    (h : ∀ u : List Bool, u.length ≤ w.length → ∀ i, lo i ≤ (N.runWith u c).workTapePos i ∧
      (N.runWith u c).workTapePos i ≤ hi i) :
    N.spaceUsedWith w c ≤ ∑ i, (hi i - lo i + 1).toNat := by
  unfold NDTM.spaceUsedWith
  refine Finset.sum_le_sum fun i _ => ?_
  have hsub : N.visitedWith w c i ⊆ Finset.Icc (lo i) (hi i) := by
    intro z hz
    simp only [NDTM.visitedWith, Finset.mem_image, Finset.mem_range] at hz
    obtain ⟨j, hj, rfl⟩ := hz
    rw [Finset.mem_Icc]
    exact h _ (by simp) i
  refine (Finset.card_le_card hsub).trans (le_of_eq ?_)
  rw [Int.card_Icc]
  congr 1
  ring

end Generic

/-! ## The compiled nondeterministic machine -/

section Construction

variable {m d kD : ℕ} {Λ SD : Type}

/-- The targets of the `choose` whose fragment starts at a compiled state (`none` elsewhere). -/
def nchoice (A : NARM m d Λ) : CSt (Λ × Ph) SD m → Option (Λ × Λ)
  | .prog (l, ph) => if ph = .start then (A l).targets else none
  | _ => none

/-- A compiled state with `choose` targets is the start state of a `choose` fragment. -/
lemma nchoice_spec {A : NARM m d Λ} {q : CSt (Λ × Ph) SD m} {l₁ l₀ : Λ}
    (h : nchoice A q = some (l₁, l₀)) : ∃ l, q = .prog (l, .start) ∧ A l = .choose l₁ l₀ := by
  match q, h with
  | .prog (l, ph), h =>
    simp only [nchoice] at h
    split_ifs at h with hph
    · subst hph
      refine ⟨l, rfl, ?_⟩
      cases hA : A l with
      | det i => rw [hA] at h; simp [NIns.targets] at h
      | choose a b => rw [hA] at h; simp only [NIns.targets, Option.some.injEq,
          Prod.mk.injEq] at h; rw [h.1, h.2]

/-- **The compiled nondeterministic machine** of a nondeterministic abstract register machine
`A` with start label `l₀`, calling the deciders `D` from the start states `q0 j`: at the start
state of a `choose l₁ l₀'` fragment, choice bit `b` moves to the start of `l₁` (if `b`) or
`l₀'`; everywhere else both choices make the step of the compiled deterministic part. -/
def ncompileTM (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) :
    NDTM (m + kD) Bool (CSt (Λ × Ph) SD m) where
  q₀ := .prog (l₀, .start)
  tr b q a w :=
    match nchoice A q with
    | some (l₁, l₀') => goAct (.prog ((if b then l₁ else l₀'), .start))
    | none => ctr (armProg (A.detPart false) l₀) D q0 q a w

/-- The compiled nondeterministic machine as a bundled finite nondeterministic machine. -/
def ncompileFinNDTM [Fintype Λ] [DecidableEq Λ] [Fintype SD] [DecidableEq SD]
    (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) : FinNDTM Bool where
  k := m + kD
  State := CSt (Λ × Ph) SD m
  tm := ncompileTM A l₀ D q0

/-- The transition table of a compiled program depends on the program only through its call
nodes, and its transitions at the program states visited. -/
lemma ctr_congr {Λ' : Type} {P P' : RProg m d Λ'} (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (q : CSt Λ' SD m) (hcall : P.call = P'.call)
    (htr : ∀ s, q = .prog s → P.tm.tr s = P'.tm.tr s) : ctr P D q0 q = ctr P' D q0 q := by
  funext a w
  cases q with
  | prog s => simp only [ctr, hcall, htr s rfl]
  | sim l q s par dir res => simp only [ctr, hcall]
  | ret1 l s dir res => rfl
  | ret2 l s dir res => simp only [ctr, hcall]
  | retR l s dir res a' scan => simp only [ctr, hcall]

/-- The call nodes of the compiled deterministic parts do not depend on the answer at the
`choose` labels. -/
lemma armProg_detPart_call (A : NARM m d Λ) (l₀ : Λ) (β β' : Bool) :
    (armProg (A.detPart β) l₀).call = (armProg (A.detPart β') l₀).call := by
  funext q
  obtain ⟨l, ph⟩ := q
  show insCall (A.detPart β l) ph = insCall (A.detPart β' l) ph
  cases hA : A l with
  | det i => rw [NARM.detPart_det hA, NARM.detPart_det hA]
  | choose l₁ l₀' => rw [NARM.detPart_choose hA, NARM.detPart_choose hA]; rfl

/-- **Away from the `choose` start states, both choices of the compiled nondeterministic
machine make the step of the compiled deterministic part `A.detPart β`**, for either `β`. -/
lemma ncompileTM_tr (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    {q : CSt (Λ × Ph) SD m} (hq : nchoice A q = none) (b β : Bool) :
    (ncompileTM A l₀ D q0).tr b q =
      (compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0).tr q := by
  funext a w
  simp only [ncompileTM, compileTM, hq]
  rw [ctr_congr D q0 q (armProg_detPart_call A l₀ false β) ?_]
  rintro ⟨l, ph⟩ rfl
  funext a' w'
  show insTr (A.detPart false l) l ph a' w' = insTr (A.detPart β l) l ph a' w'
  cases hA : A l with
  | det i => rw [NARM.detPart_det hA, NARM.detPart_det hA]
  | choose l₁ l₀' =>
    have hph : ph ≠ .start := by
      rintro rfl; simp [nchoice, hA, NIns.targets] at hq
    rw [NARM.detPart_choose hA, NARM.detPart_choose hA]
    cases ph <;> first | exact absurd rfl hph | rfl

/-- **At a `choose` start state the compiled deterministic part halts at once, writing `β`.** -/
lemma detPart_step_choose (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) (β : Bool) {x : List Bool} (c : Cfg (m + kD) Bool (CSt (Λ × Ph) SD m) x)
    (q : CSt (Λ × Ph) SD m) (hc : c.state = some q) (hq : nchoice A q ≠ none) :
    ((compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0).step c).state = none ∧
      ((compileTM (armProg (A.detPart β) l₀) (l₀, .start) D q0).step c).output =
        c.output ++ [β] := by
  obtain ⟨⟨l₁, l₀'⟩, hq'⟩ := Option.ne_none_iff_exists'.mp hq
  obtain ⟨l, rfl, hA⟩ := nchoice_spec hq'
  have hcall : (armProg (A.detPart β) l₀).call (l, .start) = none := by
    show insCall (A.detPart β l) .start = none
    rw [NARM.detPart_choose hA]; rfl
  have htr : ∀ a w, (armProg (A.detPart β) l₀).tm.tr (l, .start) a w = retAct β := by
    intro a w
    show insTr (A.detPart β l) l .start a w = retAct β
    rw [NARM.detPart_choose hA]; rfl
  unfold MultiTapeTM.step
  rw [hc]
  simp only [compileTM, ctr, hcall, htr, retAct, Action.apply]
  exact ⟨rfl, by simp⟩

/-- **A `choose` is one control step** of the compiled nondeterministic machine: from the
compiled program configuration at `l` the choice bit `b` moves to that at `l₁` or `l₀'`. -/
lemma ncompileTM_stepWith_choose (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD)
    (q0 : Fin d → SD) {x : List Bool} {l l₁ l₀' : Λ} (hA : A l = .choose l₁ l₀') (b : Bool)
    (v : Fin m → ℕ) (out : List Bool) :
    (ncompileTM A l₀ D q0).stepWith b (seam (kD := kD) (SD := SD) (aseam x l v out)) =
      seam (aseam x (if b then l₁ else l₀') v out) := by
  have hs : (seam (kD := kD) (SD := SD) (aseam x l v out)).state = some (.prog (l, .start)) :=
    rfl
  have hn : nchoice (SD := SD) A (.prog (l, .start)) = some (l₁, l₀') := by
    simp [nchoice, hA, NIns.targets]
  unfold NDTM.stepWith
  rw [hs]
  simp only [ncompileTM, hn]
  refine Cfg.ext ?_ ?_ ?_ ?_ ?_
  · simp [goAct, Action.apply, seam, aseam]
  · simp [goAct, Action.apply, seam, aseam]
  · funext i; simp [goAct, Action.apply, seam, aseam]
  · funext i; simp [goAct, Action.apply, seam, aseam]
  · simp [goAct, Action.apply, seam, aseam]

/-- The initial configuration of the compiled nondeterministic machine is the compiled program
configuration of the start label with all registers `0`. -/
lemma ncompileTM_init (A : NARM m d Λ) (l₀ : Λ) (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD)
    (x : List Bool) :
    (ncompileTM A l₀ D q0).initCfg x = seam (aseam x l₀ (fun _ => 0) []) := by
  rw [← init_eq_aseam]
  exact seam_init (armProg (A.detPart false) l₀) (l₀, .start) D q0 x

end Construction

/-! ## Deterministic steps on every branch -/

section Steps

variable {m d kD : ℕ} {Λ SD : Type} {x : List Bool}

/-- A compiled configuration with register heads in `[-1, W]` and decider heads in `[-B, B]`. -/
def NBox {St : Type} (W B : ℕ) (C : Cfg (m + kD) Bool St x) : Prop :=
  (∀ r : Fin m, (-1 : ℤ) ≤ C.workTapePos (Fin.castAdd kD r) ∧
    C.workTapePos (Fin.castAdd kD r) ≤ W) ∧
  ∀ i : Fin kD, |C.workTapePos (Fin.natAdd m i)| ≤ B

/-- The compiled program configuration of an abstract configuration is in the box. -/
lemma nbox_seam {St : Type} (W B : ℕ) (l : Λ) (v : Fin m → ℕ) (out : List Bool) :
    NBox (kD := kD) (St := CSt (Λ × Ph) St m) W B (seam (aseam x l v out)) :=
  ⟨fun r => by simp [seam, aseam], fun i => by simp [seam]⟩

/-- **A live deterministic step on every branch.** If, at a deterministic label, the abstract
machine steps from `(l, v)` to the live `(l', v')`, with the preconditions and register widths
of `arm_step`, then there is `S` such that every choice word of length `S` drives the compiled
nondeterministic machine from the compiled configuration of `(l, v)` to that of `(l', v')`,
every word of length at most `S` staying in the box.

**Proof sketch.** `arm_step` for `A.detPart false` and `compile_correct_from` give a run of
the compiled deterministic part `M` reaching the seam of `(l', v')`, in the box. It ends live,
so it avoids the `choose` start states (`avoid_of_live`, `detPart_step_choose`), and every
branch follows it (`ndtm_runWith_eq_runFrom`, `ncompileTM_tr`). -/
theorem ndet_live (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (l l' : Λ) (v v' : Fin m → ℕ)
    (out : List Bool)
    (hs : astep (A.detPart false) oracle x (some l, v, none) = (some l', v', none))
    (hp : NPre A oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    ∃ S, (∀ u : List Bool, u.length ≤ S →
        NBox W B ((ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)))) ∧
      ∀ u : List Bool, u.length = S →
        (ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)) = seam (aseam x l' v' out) := by
  obtain ⟨T, e, hinv⟩ := arm_step (A.detPart false) l₀ oracle D q0 B W l l' v v' out hs hp hw
  obtain ⟨S, hS, hb⟩ := compile_correct_from (armProg (A.detPart false) l₀) (l₀, .start) D q0
    oracle (fun _ => -1) (fun _ => (W : ℤ)) B (aseam x l v out) T
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hinv t h).1 r
      · obtain rfl : t = T := by omega
        rw [e]; simp [aseam])
    (fun t ht => (hinv t ht).2)
  set M := compileTM (armProg (A.detPart false) l₀) (l₀, .start) D q0
  have hX := avoid_of_live M (fun q => nchoice A q ≠ none)
    (fun c q hc hq => (detPart_step_choose A l₀ D q0 false c q hc hq).1)
    (seam (aseam x l v out)) S (by rw [hS, e]; simp [seam, aseam])
  have hag := ndtm_runWith_eq_runFrom (ncompileTM A l₀ D q0) M (fun q => nchoice A q ≠ none)
    (fun b q hq => ncompileTM_tr A l₀ D q0 (not_not.mp hq) b false) _ S hX
  refine ⟨S, fun u hu => ?_, fun u hu => ?_⟩
  · rw [hag u hu]; exact hb u.length hu
  · rw [hag u hu.le, hu, hS, e]

/-- **A halting deterministic step on every branch.** If, at a deterministic label, the
abstract machine halts from `(l, v)` with answer `b₀`, with the preconditions and register
widths of `arm_run`, then there are `S` and a halted configuration with output `out ++ [b₀]`
reached by every choice word of length `S` from the compiled configuration of `(l, v)`, every
word of length at most `S` staying in the box.

**Proof sketch.** As `ndet_live`, with `arm_run` (one step) for the deterministic part
`A.detPart (!b₀)`: its run ends with answer `b₀ ≠ !b₀`, so it avoids the `choose` start states,
where it would answer `!b₀` (`avoid_of_halt`). -/
theorem ndet_halt (A : NARM m d Λ) (l₀ : Λ) (oracle : Fin d → List Bool → Bool)
    (D : MultiTapeTM kD Bool SD) (q0 : Fin d → SD) (B W : ℕ) (l : Λ) {i : Ins m d Λ}
    (hA : A l = .det i) (v : Fin m → ℕ) (out : List Bool) (b₀ : Bool)
    (hs : astep (A.detPart false) oracle x (some l, v, none) = (none, v, some b₀))
    (hp : NPre A oracle D q0 B x (some l, v, none))
    (hw : ∀ r, ((Nat.bits (v r + 1)).length : ℤ) ≤ W) :
    ∃ S Cf, (∀ u : List Bool, u.length ≤ S →
        NBox W B ((ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)))) ∧
      (∀ u : List Bool, u.length = S →
        (ncompileTM A l₀ D q0).runWith u (seam (aseam x l v out)) = Cf) ∧
      Cf.state = none ∧ Cf.output = out ++ [b₀] := by
  have hs' : astep (A.detPart (!b₀)) oracle x (some l, v, none) = (none, v, some b₀) := by
    rw [← nastep_det hA (!b₀) false, nastep_det hA false false]; exact hs
  obtain ⟨T, e1, e2, e3, hinv⟩ := arm_run (x := x) (A.detPart (!b₀)) l₀ oracle D q0 B W 1 l v out b₀
    (by simp [arun, hs']) (by simp [arun, hs'])
    (fun t ht => by
      obtain rfl : t = 0 := by omega
      exact ⟨(pre_detPart D q0 B (!b₀) _).2 hp, hw⟩)
  obtain ⟨S, hS, hb⟩ := compile_correct_from (armProg (A.detPart (!b₀)) l₀) (l₀, .start) D q0
    oracle (fun _ => -1) (fun _ => (W : ℤ)) B (aseam x l v out) T
    (fun t ht r => by
      rcases Nat.lt_or_ge t T with h | h
      · exact (hinv t h).1 r
      · obtain rfl : t = T := by omega
        exact e3 r)
    (fun t ht => (hinv t ht).2)
  set M := compileTM (armProg (A.detPart (!b₀)) l₀) (l₀, .start) D q0
  have hX := avoid_of_halt M (fun q => nchoice A q ≠ none) (!b₀)
    (fun c q hc hq => detPart_step_choose A l₀ D q0 (!b₀) c q hc hq)
    (seam (aseam x l v out)) S b₀ (by rw [hS]; exact e2) (by cases b₀ <;> simp)
  have hag := ndtm_runWith_eq_runFrom (ncompileTM A l₀ D q0) M (fun q => nchoice A q ≠ none)
    (fun b q hq => ncompileTM_tr A l₀ D q0 (not_not.mp hq) b (!b₀)) _ S hX
  refine ⟨S, seam (rrun (armProg (A.detPart (!b₀)) l₀) oracle (aseam x l v out) T),
    fun u hu => ?_, fun u hu => ?_, seam_state_none _ e1, e2⟩
  · rw [hag u hu]; exact hb u.length hu
  · rw [hag u hu.le, hu, hS]

end Steps

end Complexity.LogProg
