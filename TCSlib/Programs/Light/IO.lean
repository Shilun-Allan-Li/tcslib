/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Programs.Light.IO.Exec
import TCSlib.Programs.Light.Calls
import TCSlib.Programs.Light.Renumber
import TCSlib.Programs.Light.RunsStayInLimits

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Input, output and coins in Light

The input, output and random-bit extension of the Light language of [AFM26].

## Main definitions

`EndsIO` records output and the consumed stream prefix; `MeetsIO` specifies procedures.
`Stmt.silent`, `Stmt.calls` and `Program.SilentSet` describe code with empty traces.

## Main results

Stream-aware statement rules, silent-code lifting, relocation and finite-stream bounds.
`IO.Exec` supplies trace lengths, determinism and execution inversions.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, folder `3sum-apsp`,
  commit e1a4e6508154ea59f030480661590a9fe3018011, Apache-2.0: the language extended here.
-/

namespace Light

/-- `EndsIO lim P d s σ ρ T Q`: with the coin stream `ρ`, the statement `s`, started in `σ`,
ends within `T` steps in a state `σ'`, having emitted `o` and consumed a prefix `r` of `ρ`, with
`Q σ' o r`. By `Exec.det` there is at most one such run. -/
def EndsIO (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (ρ : List Bool) (T : ℕ)
    (Q : State → List Bool → List Bool → Prop) : Prop :=
  ∃ σ' o r c, Exec lim P d s σ σ' o r c ∧ r <+: ρ ∧ c ≤ T ∧ Q σ' o r


/-- Reading `EndsIO`: the witnesses a downstream proof inspects are a run, a consumed
word that is a prefix of the stream, its cost within `T`, and `Q` of the end state, output and
consumed word. -/
theorem endsIO_iff (lim : Limits) (P : Program) (d : ℕ) (s : Stmt) (σ : State) (ρ : List Bool)
    (T : ℕ) (Q : State → List Bool → List Bool → Prop) :
    EndsIO lim P d s σ ρ T Q ↔
      ∃ σ' o r c, Exec lim P d s σ σ' o r c ∧ r <+: ρ ∧ c ≤ T ∧ Q σ' o r := Iff.rfl

/-! ## Private transports of run witnesses -/

/-- The old logic supplies the postcondition when every possible run has empty traces. -/
private theorem of_empty {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State}
    {ρ : List Bool} {T : ℕ} {Q : State → List Bool → List Bool → Prop}
    (h : Ends lim P d s σ T fun σ' => Q σ' [] [])
    (hn : ∀ σ' o r c, Exec lim P d s σ σ' o r c → o = [] ∧ r = []) :
    EndsIO lim P d s σ ρ T Q := by
  obtain ⟨σ', o, r, c, he, ht, hq⟩ := (ends_iff ..).mp h
  obtain ⟨rfl, rfl⟩ := hn _ _ _ _ he
  exact ⟨σ', [], [], c, he, List.nil_prefix, ht, hq⟩

/-- Transport a stream-preserving run rule, adding a fixed overhead to its cost. -/
private theorem map_run {lim : Limits} {P : Program} {d d' : ℕ} {s s' : Stmt}
    {σ σ₀ : State} {ρ : List Bool} {T T' K : ℕ} {F : State → State}
    {Q Q' : State → List Bool → List Bool → Prop}
    (h : EndsIO lim P d s σ ρ T Q)
    (he : ∀ σ' o r c, Exec lim P d s σ σ' o r c →
      Exec lim P d' s' σ₀ (F σ') o r (K + c))
    (hq : ∀ σ' o r, Q σ' o r → Q' (F σ') o r) (ht : K + T ≤ T') :
    EndsIO lim P d' s' σ₀ ρ T' Q' := by
  obtain ⟨σ', o, r, c, run, hr, hc, hQ⟩ := (endsIO_iff ..).mp h
  exact ⟨F σ', o, r, K + c, he _ _ _ _ run, hr, by omega, hq _ _ _ hQ⟩

section Rules

variable {lim : Limits} {P : Program} {d : ℕ} {σ : State} {ρ : List Bool} {T : ℕ}
  {Q : State → List Bool → List Bool → Prop}

/-- An `EndsIO` fact is an `Ends` fact. -/
theorem EndsIO.toEnds {s : Stmt} {Q' : State → Prop} (h : EndsIO lim P d s σ ρ T Q)
    (hQ : ∀ σ' o r, Q σ' o r → Q' σ') : Ends lim P d s σ T Q' := by
  obtain ⟨σ', o, r, c, he, _, ht, hq⟩ := (endsIO_iff ..).mp h
  exact (ends_iff ..).mpr ⟨σ', o, r, c, he, ht, hQ _ _ _ hq⟩

/-- An `EndsIO` fact holds with more time and any weaker conclusion. -/
theorem EndsIO.mono {s : Stmt} {T' : ℕ} {Q' : State → List Bool → List Bool → Prop}
    (h : EndsIO lim P d s σ ρ T Q) (hT : T ≤ T') (hQ : ∀ σ' o r, Q σ' o r → Q' σ' o r) :
    EndsIO lim P d s σ ρ T' Q' := by
  obtain ⟨σ', o, r, c, he, hr, ht, hq⟩ := (endsIO_iff ..).mp h
  exact ⟨σ', o, r, c, he, hr, ht.trans hT, hQ _ _ _ hq⟩

/-- `skip` ends at once, in its start state, emitting and consuming nothing. -/
theorem EndsIO.skip (h : Q σ [] []) : EndsIO lim P d .skip σ ρ T Q := by
  apply of_empty (Ends.skip h)
  intro σ' o r c he
  cases he
  exact ⟨rfl, rfl⟩

/-- An assignment of a safe expression ends within its cost, emitting and consuming nothing. -/
theorem EndsIO.set {x : ℕ} {e : Expr} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ) } [] []) :
    EndsIO lim P d (.set x e) σ ρ T Q := by
  apply of_empty (Ends.set hs hT h)
  intro σ' o r c he
  cases he
  exact ⟨rfl, rfl⟩

/-- A store of a safe expression at an address within the limits ends within its cost, emitting
and consuming nothing. -/
theorem EndsIO.store {a e : Expr} (ha : a.Safe lim σ) (he : e.Safe lim σ)
    (hA : lim.Addr (a.val σ)) (hT : a.cost + e.cost + 1 ≤ T)
    (h : Q { σ with mem := Function.update σ.mem (a.val σ).toNat (e.val σ) } [] []) :
    EndsIO lim P d (.store a e) σ ρ T Q := by
  apply of_empty (Ends.store ha he hA hT h)
  intro σ' o r c he
  cases he
  exact ⟨rfl, rfl⟩

/-- Sequencing: the second statement runs on the rest of the stream, and the outputs and the
consumed words are concatenated. -/
theorem EndsIO.seq {s₁ s₂ : Stmt} (T₁ T₂ : ℕ)
    (h : EndsIO lim P d s₁ σ ρ T₁ fun σ' o₁ r₁ =>
      EndsIO lim P d s₂ σ' (ρ.drop r₁.length) T₂ fun σ'' o₂ r₂ => Q σ'' (o₁ ++ o₂) (r₁ ++ r₂))
    (hT : T₁ + T₂ ≤ T) : EndsIO lim P d (.seq s₁ s₂) σ ρ T Q := by
  obtain ⟨σ', o₁, r₁, c₁, he₁, hr₁, ht₁, h₂⟩ := (endsIO_iff ..).mp h
  obtain ⟨σ'', o₂, r₂, c₂, he₂, hr₂, ht₂, hq⟩ := (endsIO_iff ..).mp h₂
  refine ⟨σ'', o₁ ++ o₂, r₁ ++ r₂, c₁ + c₂, .seq he₁ he₂, ?_, by omega, hq⟩
  rw [← List.prefix_iff_eq_append.mp hr₁]
  exact (List.prefix_append_right_inj r₁).mpr hr₂

/-- A branch: the side that the test selects, on the same stream, after the test's cost. -/
theorem EndsIO.ite {c : Cond} {s₁ s₂ : Stmt} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → EndsIO lim P d s₁ σ ρ T' Q) (h₂ : ¬ c.Holds σ → EndsIO lim P d s₂ σ ρ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : EndsIO lim P d (.ite c s₁ s₂) σ ρ T Q := by
  by_cases hc : c.Holds σ
  · exact map_run (h₁ hc) (fun _ _ _ _ he => .iteTrue hs hc he) (fun _ _ _ hq => hq) hT
  · exact map_run (h₂ hc) (fun _ _ _ _ he => .iteFalse hs hc he) (fun _ _ _ hq => hq) hT

/-- A loop whose test holds: one round on the stream, then the loop on the rest. -/
theorem EndsIO.whileStep {c : Cond} {s : Stmt} (T₁ T₂ : ℕ) (hs : c.Safe lim σ)
    (hc : c.Holds σ)
    (h : EndsIO lim P d s σ ρ T₁ fun σ' o₁ r₁ =>
      EndsIO lim P d (.while c s) σ' (ρ.drop r₁.length) T₂ fun σ'' o₂ r₂ =>
        Q σ'' (o₁ ++ o₂) (r₁ ++ r₂))
    (hT : c.cost + 1 + T₁ + T₂ ≤ T) : EndsIO lim P d (.while c s) σ ρ T Q := by
  have hseq := EndsIO.seq T₁ T₂ h (le_refl _)
  apply map_run (K := c.cost + 1) hseq _ (fun _ _ _ hq => hq) (by omega)
  intro σ' o r k he
  cases he with
  | seq h₁ h₂ =>
    simpa only [Nat.add_assoc] using Exec.whileTrue hs hc h₁ h₂

/-- A loop whose test fails ends after the test, emitting and consuming nothing. -/
theorem EndsIO.whileDone {c : Cond} {s : Stmt} (hs : c.Safe lim σ) (hc : ¬ c.Holds σ)
    (hQ : Q σ [] []) (hT : c.cost + 1 ≤ T) : EndsIO lim P d (.while c s) σ ρ T Q := by
  apply of_empty (Ends.whileDone hs hc hQ hT)
  intro σ' o r k he
  cases he with
  | whileFalse => exact ⟨rfl, rfl⟩
  | whileTrue _ hh _ _ => exact (hc hh).elim

/-- Calls: the body runs on the same stream; the output and the consumed coins pass through. -/
theorem EndsIO.call {p x : ℕ} {args : List Expr} {body : Stmt} (T' : ℕ)
    (ha : ∀ e ∈ args, e.Safe lim σ) (hp : P[p]? = some body) (hd : d < lim.depth)
    (h : EndsIO lim P (d + 1) body ⟨frame (args.map (·.val σ)), σ.mem⟩ ρ T' fun σ' o r =>
      Q ⟨Function.update σ.loc x (σ'.loc 0), σ'.mem⟩ o r)
    (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) : EndsIO lim P d (.call p args x) σ ρ T Q := by
  exact map_run h (fun _ _ _ _ he => .call ha hp hd he) (fun _ _ _ hq => hq) hT

/-- `x := inBit e` sets `x` to the input bit at the position `e` (`0` off the input), within
`e.cost + 1` steps, emitting and consuming nothing. -/
theorem EndsIO.inBit {x : ℕ} {e : Expr} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (inBitVal lim.input (e.val σ)) } [] []) :
    EndsIO lim P d (.inBit x e) σ ρ T Q := by
  exact ⟨_, [], [], _, .inBit hs, List.nil_prefix, hT, h⟩

/-- `emit e` emits the one bit "`e ≠ 0`" within `e.cost + 1` steps and changes no variable or
cell. -/
theorem EndsIO.emit {e : Expr} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q σ [decide (e.val σ ≠ 0)] []) : EndsIO lim P d (.emit e) σ ρ T Q := by
  exact ⟨_, _, [], _, .emit hs, List.nil_prefix, hT, h⟩

/-- A coin reads the first bit of the stream. -/
theorem EndsIO.coin {x : ℕ} {b : Bool} {ρ' : List Bool} (hρ : ρ = b :: ρ') (hT : 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (if b then 1 else 0) } [] [b]) :
    EndsIO lim P d (.coin x) σ ρ T Q := by
  subst ρ
  exact ⟨_, [], [b], 1, .coin b, ⟨ρ', rfl⟩, hT, h⟩

/-- `x := half e` sets `x` to `⌊e / 2⌋` within `e.cost + 1` steps, emitting and consuming
nothing. -/
theorem EndsIO.half {x : ℕ} {e : Expr} (hs : e.Safe lim σ) (hT : e.cost + 1 ≤ T)
    (h : Q { σ with loc := Function.update σ.loc x (e.val σ / 2) } [] []) :
    EndsIO lim P d (.half x e) σ ρ T Q := by
  exact ⟨_, [], [], _, .half hs, List.nil_prefix, hT, h⟩

/-- The `Ends` rule for a coin: some bit leads to `Q` (the existential reading of `Ends`). -/
theorem Ends.coin {x : ℕ} {Q' : State → Prop} (b : Bool) (hT : 1 ≤ T)
    (h : Q' { σ with loc := Function.update σ.loc x (if b then 1 else 0) }) :
    Ends lim P d (.coin x) σ T Q' := by
  exact (ends_iff ..).mpr ⟨_, [], [b], 1, .coin b, hT, h⟩

end Rules

/-! ## Specifications of procedures with input and output -/

/-- `MeetsIO lim P p d vals μ ρ T R`: procedure `p`, run at depth `d` on the arguments `vals` in
the memory `μ` with the stream `ρ`, ends within `T` steps with a result, a memory, an output and
a consumed word that satisfy `R`. The I/O counterpart of `Light.Meets` (`Calls.lean:57`), which
stays as it is. -/
def MeetsIO (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ) (ρ : List Bool)
    (T : ℕ) (R : ℤ → (ℕ → ℤ) → List Bool → List Bool → Prop) : Prop :=
  ∃ body, P[p]? = some body ∧
    EndsIO lim P d body ⟨frame vals, μ⟩ ρ T fun σ' o r => R (σ'.loc 0) σ'.mem o r

/-- Reading `MeetsIO`. -/
theorem meetsIO_iff (lim : Limits) (P : Program) (p d : ℕ) (vals : List ℤ) (μ : ℕ → ℤ)
    (ρ : List Bool) (T : ℕ) (R : ℤ → (ℕ → ℤ) → List Bool → List Bool → Prop) :
    MeetsIO lim P p d vals μ ρ T R ↔ ∃ body, P[p]? = some body ∧
      EndsIO lim P d body ⟨frame vals, μ⟩ ρ T fun σ' o r => R (σ'.loc 0) σ'.mem o r := Iff.rfl

/-- `x := p(args)` with a specification that sees the output and the coins (the I/O counterpart
of `Light.Ends.callLast`, `Calls.lean:113`). -/
theorem EndsIO.callLast {lim : Limits} {P : Program} {d p x T T' : ℕ} {loc μ : ℕ → ℤ}
    {args : List Expr} {vals : List ℤ} {ρ : List Bool}
    {R : ℤ → (ℕ → ℤ) → List Bool → List Bool → Prop} {Q : State → List Bool → List Bool → Prop}
    (hp : MeetsIO lim P p (d + 1) vals μ ρ T' R)
    (h : ∀ v μ' o r, R v μ' o r → Q ⟨Function.update loc x v, μ'⟩ o r)
    (ha : (∀ e ∈ args, e.Safe lim ⟨loc, μ⟩) ∧ args.map (·.val ⟨loc, μ⟩) = vals)
    (hd : d < lim.depth) (hT : (args.map Expr.cost).sum + 2 + T' ≤ T) :
    EndsIO lim P d (.call p args x) ⟨loc, μ⟩ ρ T Q := by
  obtain ⟨body, hb, he⟩ := (meetsIO_iff ..).mp hp
  obtain ⟨hs, rfl⟩ := ha
  exact EndsIO.call T' hs hb hd (he.mono (le_refl _) fun _ o r hR => h _ _ o r hR) hT

/-! ## Silent code and relocation -/

/-- A statement is **silent** if it contains no `emit` and no `coin` (calls are checked
separately, through a silent set). `inBit` and `half` are silent. -/
def Stmt.silent : Stmt → Bool
  | .skip => true
  | .set _ _ => true
  | .store _ _ => true
  | .seq s t => s.silent && t.silent
  | .ite _ s t => s.silent && t.silent
  | .while _ s => s.silent
  | .call _ _ _ => true
  | .inBit _ _ => true
  | .emit _ => false
  | .coin _ => false
  | .half _ _ => true

/-- The procedures a statement calls directly. -/
def Stmt.calls : Stmt → List ℕ
  | .seq s t => s.calls ++ t.calls
  | .ite _ s t => s.calls ++ t.calls
  | .while _ s => s.calls
  | .call p _ _ => [p]
  | _ => []

/-- Reading `Stmt.silent` on a sequence. -/
theorem Stmt.silent_seq (s t : Stmt) : (Stmt.seq s t).silent = (s.silent && t.silent) := rfl

/-- Reading `Stmt.silent` on a branch. -/
theorem Stmt.silent_ite (c : Cond) (s t : Stmt) :
    (Stmt.ite c s t).silent = (s.silent && t.silent) := rfl

/-- Reading `Stmt.silent` on a loop. -/
theorem Stmt.silent_while (c : Cond) (s : Stmt) : (Stmt.while c s).silent = s.silent := rfl

/-- `emit` and `coin` are the statements that are not silent. -/
theorem Stmt.silent_emit (e : Expr) : (Stmt.emit e).silent = false := rfl

@[inherit_doc Stmt.silent_emit]
theorem Stmt.silent_coin (x : ℕ) : (Stmt.coin x).silent = false := rfl

/-- Reading `Stmt.calls` on a call. -/
theorem Stmt.calls_call (p : ℕ) (args : List Expr) (x : ℕ) :
    (Stmt.call p args x).calls = [p] := rfl

/-- Reading `Stmt.silent` on the remaining leaves: all are silent. -/
theorem Stmt.silent_leaf (x p : ℕ) (a e : Expr) (args : List Expr) :
    Stmt.skip.silent = true ∧ (Stmt.set x e).silent = true ∧ (Stmt.store a e).silent = true ∧
      (Stmt.call p args x).silent = true ∧ (Stmt.inBit x e).silent = true ∧
      (Stmt.half x e).silent = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Reading `Stmt.calls` on compound statements. -/
theorem Stmt.calls_seq (s t : Stmt) : (Stmt.seq s t).calls = s.calls ++ t.calls := rfl

@[inherit_doc Stmt.calls_seq]
theorem Stmt.calls_ite (c : Cond) (s t : Stmt) :
    (Stmt.ite c s t).calls = s.calls ++ t.calls := rfl

@[inherit_doc Stmt.calls_seq]
theorem Stmt.calls_while (c : Cond) (s : Stmt) : (Stmt.while c s).calls = s.calls := rfl

/-- Reading `Stmt.calls` on the leaves other than `call`: they call nothing. -/
theorem Stmt.calls_leaf (x : ℕ) (a e : Expr) :
    Stmt.skip.calls = [] ∧ (Stmt.set x e).calls = [] ∧ (Stmt.store a e).calls = [] ∧
      (Stmt.inBit x e).calls = [] ∧ (Stmt.emit e).calls = [] ∧ (Stmt.coin x).calls = [] ∧
      (Stmt.half x e).calls = [] :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `S` is a **silent set** of `P`: its procedures exist, their bodies are silent, and they call
only procedures in `S`. -/
def Program.SilentSet (P : Program) (S : Set ℕ) : Prop :=
  ∀ p ∈ S, ∃ b, P[p]? = some b ∧ b.silent = true ∧ ∀ q ∈ b.calls, q ∈ S

/-- Reading `Program.SilentSet`. -/
theorem Program.silentSet_iff (P : Program) (S : Set ℕ) :
    P.SilentSet S ↔ ∀ p ∈ S, ∃ b, P[p]? = some b ∧ b.silent = true ∧ ∀ q ∈ b.calls, q ∈ S :=
  Iff.rfl

/-- **Silent code has empty traces.** A run of a silent statement that calls only procedures in a
silent set emits nothing and consumes nothing.

**Proof sketch.** Induction on the run. The leaves other than `emit` and `coin` have empty
traces; `seq`, `ite` and `while` inherit silence and the call condition from their parts; a call
goes to a procedure of `S`, whose body is silent and calls into `S`. -/
theorem Exec.traces_nil {lim : Limits} {P : Program} {S : Set ℕ} {d : ℕ} {s : Stmt}
    {σ σ' : State} {o r : List Bool} {c : ℕ} (hS : P.SilentSet S) (hs : s.silent = true)
    (hc : ∀ q ∈ s.calls, q ∈ S) (h : Exec lim P d s σ σ' o r c) : o = [] ∧ r = [] := by
  revert hs hc
  induction h with
  | skip => intros; exact ⟨rfl, rfl⟩
  | set => intros; exact ⟨rfl, rfl⟩
  | store => intros; exact ⟨rfl, rfl⟩
  | seq h₁ h₂ ih₁ ih₂ =>
    intro hs hc
    obtain ⟨hs₁, hs₂⟩ := Bool.and_eq_true_iff.mp hs
    have h₁ := ih₁ hs₁ (fun q hq => hc q (List.mem_append_left _ hq))
    have h₂ := ih₂ hs₂ (fun q hq => hc q (List.mem_append_right _ hq))
    simp only [h₁.1, h₁.2, h₂.1, h₂.2, List.nil_append, and_self]
  | iteTrue _ _ _ ih =>
    intro hs hc
    exact ih (Bool.and_eq_true_iff.mp hs).1 (fun q hq => hc q (List.mem_append_left _ hq))
  | iteFalse _ _ _ ih =>
    intro hs hc
    exact ih (Bool.and_eq_true_iff.mp hs).2 (fun q hq => hc q (List.mem_append_right _ hq))
  | whileFalse => intros; exact ⟨rfl, rfl⟩
  | whileTrue _ _ _ _ ih₁ ih₂ =>
    intro hs hc
    obtain ⟨ho₁, hr₁⟩ := ih₁ hs hc
    obtain ⟨ho₂, hr₂⟩ := ih₂ hs hc
    simp only [ho₁, hr₁, ho₂, hr₂, List.nil_append, and_self]
  | call ha hp hd h ih =>
    intro _ hc
    obtain ⟨b, hb, hs, hcalls⟩ := (Program.silentSet_iff ..).mp hS _
      (hc _ (List.mem_singleton_self _))
    have he := Option.some.inj (hp.symm.trans hb)
    subst b
    exact ih hs hcalls
  | inBit => intros; exact ⟨rfl, rfl⟩
  | emit => intro hs; contradiction
  | coin => intro hs; contradiction
  | half => intros; exact ⟨rfl, rfl⟩

/-- A silent set stays one when procedures are appended. -/
theorem Program.SilentSet.append {P : Program} {S : Set ℕ} (hS : P.SilentSet S)
    (R : Program) : (P ++ R).SilentSet S := by
  rw [Program.silentSet_iff] at hS ⊢
  intro p hp
  obtain ⟨b, hb, hs, hc⟩ := hS p hp
  exact ⟨b, getElem?_append_of_eq_some hb R, hs, hc⟩

/-- Relocation preserves silence and maps every direct call by the same offset.

**Proof sketch.** Induct on the statement once for both properties, using the published
`Stmt.shift_*` equations and distributing `List.map` over concatenation. -/
private theorem shift_facts (n : ℕ) (s : Stmt) :
    (s.shift n).silent = s.silent ∧ (s.shift n).calls = s.calls.map (· + n) := by
  induction s <;>
    simp_all only [Stmt.shift_skip, Stmt.shift_set, Stmt.shift_store, Stmt.shift_seq,
      Stmt.shift_ite, Stmt.shift_while, Stmt.shift_call, Stmt.shift_inBit, Stmt.shift_emit,
      Stmt.shift_coin, Stmt.shift_half, Stmt.silent, Stmt.calls, List.map_append,
      List.map_nil, List.map_cons, and_self]

/-- Shifting a statement's calls keeps it silent. -/
theorem Stmt.silent_shift (n : ℕ) (s : Stmt) : (s.shift n).silent = s.silent := (shift_facts n s).1

/-- Shifting a statement's calls shifts the procedures it calls. -/
theorem Stmt.calls_shift (n : ℕ) (s : Stmt) : (s.shift n).calls = s.calls.map (· + n) := (shift_facts n s).2

/-- **Relocation of a silent set**: `P`'s silent set, shifted, is a silent set of `P` placed
behind `Q`; `Q`'s own silent sets stay silent sets (`append`). -/
theorem Program.SilentSet.behind {P : Program} {S : Set ℕ} (hS : P.SilentSet S)
    (Q : Program) : (Program.behind Q P).SilentSet ((· + Q.length) '' S) := by
  rw [Program.silentSet_iff] at hS ⊢
  intro p hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨b, hb, hs, hc⟩ := hS q hq
  refine ⟨b.shift Q.length, Program.getElem?_behind_right Q hb, ?_, ?_⟩
  · simpa only [Stmt.silent_shift] using hs
  · intro p hp
    rw [Stmt.calls_shift] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨q, hc q hq, rfl⟩

/-- **Lifting an `Ends` fact**. An `Ends` fact about silent code that calls into a silent set holds for every stream,
with nothing emitted and nothing consumed.

**Proof sketch.** Apply the shared empty-trace transport `of_empty` to the `Ends` fact;
`Exec.traces_nil` supplies its trace condition. The transport prefixes every stream by `[]`. -/
theorem EndsIO.ofEnds {lim : Limits} {P : Program} {S : Set ℕ} {d : ℕ} {s : Stmt}
    {σ : State} {ρ : List Bool} {T : ℕ} {Q₀ : State → Prop} (hS : P.SilentSet S)
    (hs : s.silent = true) (hc : ∀ q ∈ s.calls, q ∈ S) (h : Ends lim P d s σ T Q₀) :
    EndsIO lim P d s σ ρ T fun σ' o r => Q₀ σ' ∧ o = [] ∧ r = [] := by
  apply of_empty (h.mono (le_refl _) fun _ hq => ⟨hq, rfl, rfl⟩)
  intro σ' o r c he
  exact Exec.traces_nil hS hs hc he

/-- **Lifting a procedure specification**: a library routine `p` in a silent set meets its
`Meets` specification for every stream, with empty traces. This is
how the 14 routines of `Light.Std`, placed by `behind` inside an I/O program, are used under
`EndsIO` (with `EndsIO.callLast`).

**Proof sketch.** Unfold both specifications to the body's facts and apply `EndsIO.ofEnds`
with the body's silence and calls from the silent set. -/
theorem MeetsIO.ofMeets {lim : Limits} {P : Program} {S : Set ℕ} {p d : ℕ} {vals : List ℤ}
    {μ : ℕ → ℤ} {ρ : List Bool} {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (hS : P.SilentSet S)
    (hp : p ∈ S) (h : Meets lim P p d vals μ T R) :
    MeetsIO lim P p d vals μ ρ T fun v μ' o r => R v μ' ∧ o = [] ∧ r = [] := by
  obtain ⟨b, hb, hs, hc⟩ := (Program.silentSet_iff ..).mp hS p hp
  obtain ⟨body, hbody, he⟩ := (meets_iff ..).mp h
  have heq := Option.some.inj (hb.symm.trans hbody)
  subst body
  exact (meetsIO_iff ..).mpr ⟨b, hb, EndsIO.ofEnds hS hs hc he⟩

/-! ## Finite streams and permanent checks -/

/-- An `EndsIO` fact within `T` steps depends only on the first `T` bits of the stream.

**Proof sketch.** The consumed word has length at most the cost, hence at most `T`; a word of
length at most `T` is a prefix of `ρ` exactly when it is a prefix of `ρ.take T`. -/
theorem EndsIO.take_iff {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ : State}
    {ρ : List Bool} {T : ℕ} {Q : State → List Bool → List Bool → Prop} :
    EndsIO lim P d s σ ρ T Q ↔ EndsIO lim P d s σ (ρ.take T) T Q := by
  constructor
  · intro h
    rcases h with ⟨σ', o, r, c, he, hr, ht, hq⟩
    exact (endsIO_iff ..).mpr ⟨σ', o, r, c, he,
      List.prefix_take_iff.mpr ⟨hr, he.coins_length_le.trans ht⟩, ht, hq⟩
  · intro h
    rcases h with ⟨σ', o, r, c, he, hr, ht, hq⟩
    exact (endsIO_iff ..).mpr ⟨σ', o, r, c, he, hr.trans (List.take_prefix _ _), ht, hq⟩

/-- Input reads at the boundary: on `[true]`, positions `-1`, `0`, `1` read `0`, `1`, `0`. -/
theorem inBitVal_boundary :
    inBitVal [true] (-1) = 0 ∧ inBitVal [true] 0 = 1 ∧ inBitVal [true] 1 = 0 := by
  simp only [inBitVal_eq]
  decide

/-- `half` rounds down, as the arithmetic shift does: `⌊-3/2⌋ = -2`, `⌊-1/2⌋ = -1`. -/
theorem half_boundary : (-3 : ℤ) / 2 = -2 ∧ (-1 : ℤ) / 2 = -1 := by
  decide

/-- Two coins in sequence consume both, in order. -/
theorem check_two_coins (lim : Limits) (P : Program) (d : ℕ) (σ : State) :
    ∃ σ'', Exec lim P d (.seq (.coin 0) (.coin 1)) σ σ'' [] [true, false] 2 := by
  exact ⟨_, Exec.seq (Exec.coin true) (Exec.coin false)⟩

/-- Determinism fixes the consumed word's length, even when two runs are offered with words of
different lengths: they cannot both be prefixes of one stream. -/
theorem check_det_length {lim : Limits} {P : Program} {d : ℕ} {s : Stmt} {σ σ₁ σ₂ : State}
    {o₁ o₂ r₁ r₂ : List Bool} {c₁ c₂ : ℕ} {ρ : List Bool}
    (h₁ : Exec lim P d s σ σ₁ o₁ r₁ c₁) (h₂ : Exec lim P d s σ σ₂ o₂ r₂ c₂)
    (hr₁ : r₁ <+: ρ) (hr₂ : r₂ <+: ρ) (hne : r₁.length ≠ r₂.length) : False := by
  exact hne (congrArg List.length (Exec.det h₁ h₂ hr₁ hr₂).2.2.1)

/-- `Exec.bounded` needs `1 ≤ lim.word`: at word limit `0`, `coin` with the bit `true`
leaves a bounded state for an unbounded one. -/
theorem check_bounded_needs_word :
    ∃ (lim : Limits) (σ σ' : State), lim.word = 0 ∧ σ.Bounded lim ∧
      Exec lim [] 0 (.coin 0) σ σ' [] [true] 1 ∧ ¬ σ'.Bounded lim := by
  let lim : Limits := ⟨0, 0, 0, []⟩
  let σ : State := ⟨fun _ => 0, fun _ => 0⟩
  refine ⟨lim, σ, { σ with loc := Function.update σ.loc 0 1 }, rfl, ?_, .coin true, ?_⟩
  · exact (State.bounded_iff ..).mpr ⟨fun _ => by change (0 : ℤ) ≤ 0; exact le_rfl,
      fun _ => by change (0 : ℤ) ≤ 0; exact le_rfl⟩
  · intro h
    have hv := ((State.bounded_iff ..).mp h).1 0
    change |Function.update σ.loc 0 1 0| ≤ 0 at hv
    rw [Function.update_self] at hv
    norm_num at hv

end Light
