/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic
import TCSlib.Complexity.TuringMachine.Build.Seam

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Framed contracts: seams, the phase host and the release adapter

**Status: proved; landed with MIG-0b, whose gate closed at round 2 (2026-10-14)**
(`audits/mig0b-findings.md`, `audits/mig0b-r2-findings.md`; resolutions
`audits/mig0b-resolutions.md`, `audits/mig0b-r2-resolutions.md`). The
MIG-0a compositions over `Build/Seam` (`seq`, `inPhase`, `branch` and `ReturnContract.release`)
moved here from `Build/Contract.lean` as landed on 2026-10-13, with no statement changed; with
MIG-0b's round release, the joint trajectories and frames of these compositions, and their
positivity.

**Routing.** `Turing.Contract.seq` is the single-live-exit seam, `Turing.Contract.branch` the
binary case, and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live
exits, several of which may share one continuation. A first phase that halts cannot resume
through a seam, which dispatches only at a live anchor.

## Main definitions

* `Turing.Contract.seq`: sequencing through the R2 seam `Turing.seamCompTM`, after a first
  phase with a single live exit.
* `Turing.Contract.inPhase`: a phase run inside the phase host `Turing.phaseHostTM`, with an
  arbitrary set of live exits, each redirected; `Turing.Cfg.bindState`, its redirect.
* `Turing.Contract.branch`: the two-way seam `Turing.seamCompTM₂`, after a first phase with two
  live exits.
* `Turing.ReturnContract.release`, `Turing.RoundContract.release`: returning modules and rounds
  through the release adapter `Turing.seamReleaseTM`.

## Main results

* `Turing.Contract.Traj.seq`, `Turing.Contract.Traj.inPhase`, `Turing.Contract.Traj.branch`,
  `Turing.Contract.Frames.seq`: preservation of joint trajectories and frames.
* `Turing.Contract.seq_positive`, `Turing.Contract.inPhase_positive`,
  `Turing.Contract.branch_positive`, `Turing.ReturnContract.release_positive`,
  `Turing.RoundContract.release_positive`: positivity.
* `Turing.Contract.seq_pre`, `Turing.Contract.inPhase_time`, `Turing.Contract.branch_post`
  and the rest — the specification API (user, 2026-10-16): the composites' data fields as
  equations, without the `simp` attribute.
* `Turing.ReturnContract.release_pre`, `_time`, `_post`, `_lo`, `_hi` and
  `Turing.RoundContract.release_pre` … `_hi` — the release adapters' data fields as equations,
  the same way (the specification API's gate, finding 1).

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the specification-only calls adapted as `Turing.Contract` (design adaptation; full
  entry in `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

namespace Contract

section Compose

private lemma mapState_state {S S' : Type} {x : List Γ} (f : S → S') (c : Cfg k Γ S x) :
    (c.mapState f).state = c.state.map f := rfl

/-- The composed start is the left-mapped first-phase start. -/
private lemma mapState_const_inl {S₁ S₂ : Type} {x : List Γ} {e : S₁}
    {d : Cfg k Γ (S₁ ⊕ S₂) x} (hd : d.state = some (Sum.inl e)) :
    (d.mapState fun _ => e).mapState Sum.inl = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The seam trajectory of a contract run: the left segment up to the first exit (live
throughout), and the right segment after the dispatch, at every offset. The composite starts
at `Sum.inl entry₁`; the first phase runs from that start with its state replaced by `entry₁`.

**Proof sketch.** Re-tagging the replaced start by `Sum.inl` gives back the composite start.
`C₁`'s cut is the strict exit cut of `Turing.seamCompTM_runFrom_left`, which gives the left
segment up to `t₁`. It is live: a halt before `t₁` would persist to the endpoint, which is at
`exit₁`. The right segment is `Turing.seamCompTM_run_ofCfg` with second-phase time `v` and that
run's endpoint taken to be itself. The replaced endpoint is at `entry₂` by construction. -/
private lemma seq_traj {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} (entry₂ : S₂) {ι : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (i : ι) (d : Cfg k Γ (S₁ ⊕ S₂) x)
    (hd : d.state = some (Sum.inl entry₁)) (hp : C₁.pre i (d.mapState fun _ => entry₁)) :
    (∀ u ≤ C₁.time i (d.mapState fun _ => entry₁),
      (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d u =
          (M₁.runFrom (d.mapState fun _ => entry₁) u).mapState Sum.inl ∧
        (M₁.runFrom (d.mapState fun _ => entry₁) u).state ≠ none) ∧
    (∀ v, (seamCompTM M₁ exit₁ M₂ entry₂).runFrom d
        (C₁.time i (d.mapState fun _ => entry₁) + 1 + v) =
      (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
        v).mapState Sum.inr) ∧
    ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂).state =
      some entry₂ := by
  have hd' := mapState_const_inl (S₂ := S₂) hd
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have h1 := C₁.run i _ hd₁ hp
  have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
  have hcut : ∀ t < C₁.time i (d.mapState fun _ => entry₁),
      (M₁.runFrom (d.mapState fun _ => entry₁) t).state ≠ some exit₁ :=
    fun t ht => C₁.cut i _ hd₁ hp t ht
  refine ⟨fun u hu => ⟨?_, ?_⟩, fun v => ?_, by rw [mapState_state, hx]; rfl⟩
  · have hl := seamCompTM_runFrom_left M₁ exit₁ M₂ entry₂ hcut u hu
    rwa [hd'] at hl
  · refine MultiTapeTM.runFrom_state_ne_none_of_le M₁ _ _ ?_ u hu
    rw [h1, hx]
    exact Option.some_ne_none _
  · have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ h1 hx hcut (T₂ := v) rfl
    rwa [hd'] at hr

/-- **Sequencing through the R2 seam** (`Turing.seamCompTM_run_ofCfg`,
`Turing.seamCompTM_firstReturn_ofCfg`): run `C₁` to its single live exit `exit₁`, take one
stationary dispatch step, and run `C₂`, so the time is `t₁ + 1 + t₂`. The second phase starts
from the first's endpoint with its state replaced by `entry₂`; the endpoint and the exits are
right-tagged, and the envelopes take the hull.

This is the **single-live-exit seam**. Two live exits go through `Turing.Contract.branch`, and
an arbitrary set of live exits through the phase host (`Turing.Contract.inPhase`). A first phase
that halts cannot resume through a seam, which dispatches only at a live anchor.

**Proof sketch.** By the seam trajectory (`seq_traj`): up to `t₁` the composite is the
left-tagged first phase, live throughout, and at `t₁ + 1 + v` it is the right-tagged second
phase at `v`, from its entry. The run is `Turing.seamCompTM_run_ofCfg` with `C₂`'s run, and the
exit is `C₂`'s, right-tagged. For the cut, a time up to `t₁` carries a live left-tagged state,
which is no right-tagged exit; a later time is `t₁ + 1 + v` with `v < t₂`, and injectivity of the
right tag reduces it to `C₂`'s cut at `v`. The envelope is `C₁`'s up to `t₁` and `C₂`'s after
the dispatch (offset `0` is the dispatch step), inside the hull. -/
def seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)} {ι κ : Type} {x : List Γ}
    (C₁ : Contract M₁ entry₁ {some exit₁} ι x) (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM M₁ exit₁ M₂ entry₂) (Sum.inl entry₁) (Option.map Sum.inr '' X₂) ι x where
  pre i d := C₁.pre i (d.mapState fun _ => entry₁)
  time i d := C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)
  post i d :=
    (C₂.post (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂)).mapState
      Sum.inr
  lo i d j := min (C₁.lo i (d.mapState fun _ => entry₁) j)
    (C₂.lo (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  hi i d j := max (C₁.hi i (d.mapState fun _ => entry₁) j)
    (C₂.hi (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hd' := mapState_const_inl (S₂ := S₂) hd
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hx := Set.mem_singleton_iff.mp (C₁.exit_mem i _ hd₁ hp)
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    have hr := seamCompTM_run_ofCfg M₁ exit₁ M₂ entry₂ (C₁.run i _ hd₁ hp) hx
      (fun t ht => C₁.cut i _ hd₁ hp t ht) (C₂.run _ _ hd₂ (hlink i _ hd₁ hp))
    rw [hd'] at hr
    exact hr
  exit_mem i d hd hp := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
    exact ⟨_, C₂.exit_mem _ _ hd₂ (hlink i _ hd₁ hp), rfl⟩
  cut i d hd hp u hu := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u < C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    rintro ⟨q, hq, heq⟩
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · obtain ⟨hrun, hlive⟩ := hL u hle
      rw [hrun] at heq
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rw [mapState_state, hs] at heq
      cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v] at heq
      have hq' : q = (M₂.runFrom ((C₁.post i (d.mapState fun _ => entry₁)).mapState
          fun _ => entry₂) v).state := Option.map_injective Sum.inr_injective heq
      exact C₂.cut _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) (hq' ▸ hq)
  env i d hd hp u hu j := by
    have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
    change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
      C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
    by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
    · rw [(hL u hle).1]
      exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₁.env i _ hd₁ hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
        ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
      rw [hR v]
      exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
        (C₂.env _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) j)

/-- Re-type a configuration's control state through a partial map: the phase host's redirect.
A halted configuration stays halted; every other field is kept. -/
def _root_.Turing.Cfg.bindState {S S' : Type} {x : List Γ} (d : Cfg k Γ S x) (f : S → Option S') :
    Cfg k Γ S' x :=
  ⟨d.state.bind f, d.inputPos, d.workTapes, d.workTapePos, d.output⟩

/-- The phase-host trajectory of a contract run: the tagged prefix through the phase's exit,
the redirected endpoint one dispatch step later, and the live exit state.

**Proof sketch.** The endpoint's state lies in `X`, which excludes `none`, so it is a live exit
`s'`, which `red p` redirects (`hsome`). Before the endpoint the cut keeps every state out of
`X`, so `hred` says that none of them is redirected. `Turing.phaseHostTM_run` then gives the
prefix tagged with `p` up to the time and, one dispatch step later, the endpoint with its state
replaced by the target of `s'`, which is the endpoint's state bound through `red p`. The
other-phase clause of `hsome` is not used here. -/
private lemma inPhase_traj {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p)
    (i : ι) (d : Cfg k Γ (Σ i, Ph i) x) (hd : d.state = some ⟨p, s₀⟩)
    (hp : C.pre i (d.mapState fun _ => s₀)) :
    (∀ u ≤ C.time i (d.mapState fun _ => s₀),
      (phaseHostTM Mf q0 red).runFrom d u =
        ((Mf p).runFrom (d.mapState fun _ => s₀) u).mapState (Sigma.mk p)) ∧
    (phaseHostTM Mf q0 red).runFrom d (C.time i (d.mapState fun _ => s₀) + 1) =
      (C.post i (d.mapState fun _ => s₀)).bindState (red p) ∧
    ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' ∧ some s' ∈ X := by
  have hd' : (d.mapState fun _ => s₀).mapState (Sigma.mk p) = d :=
    Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  have hx := C.exit_mem i _ hc hp
  obtain ⟨s', hs'⟩ : ∃ s', (C.post i (d.mapState fun _ => s₀)).state = some s' := by
    cases h : (C.post i (d.mapState fun _ => s₀)).state with
    | none => rw [h] at hx; exact absurd hx hnone
    | some s' => exact ⟨s', rfl⟩
  have hs'X : some s' ∈ X := by rw [← hs']; exact hx
  obtain ⟨q', hq', -⟩ := hsome s' hs'X
  have H := phaseHostTM_run Mf q0 red p (d.mapState fun _ => s₀) _ _ (C.run i _ hc hp) s' hs'
    q' hq' (fun u hu s hs => hred s (fun hm => C.cut i _ hc hp u hu (by rw [hs]; exact hm)))
  rw [hd'] at H
  refine ⟨H.1, ?_, s', hs', hs'X⟩
  rw [H.2]
  refine Cfg.ext ?_ rfl rfl rfl rfl
  show Option.map (fun _ => q') (C.post i (d.mapState fun _ => s₀)).state =
    (C.post i (d.mapState fun _ => s₀)).state.bind (red p)
  rw [hs']
  simp [hq']

/-- **A phase inside the phase host** (`Turing.phaseHostTM_run`). Phase `p` runs under its own
contract, whose exits are live (`hnone`) and are exactly the states of phase `p` that the host
redirects (`hred`, `hsome`), each to a state of another phase. The host's exits are the
redirect targets, the time gains one dispatch step, and the envelopes are the phase's. The
phase host thus handles an **arbitrary set of live exits**, each sent to its own target, and
several may share one continuation; `Turing.Contract.seq` and `Turing.Contract.branch` are the
one- and two-exit seams.

The other-phase condition `q.1 ≠ p` is **sufficient, not necessary**. What the cut needs is that
the run avoids every redirect target up to its endpoint; up to there the host run is tagged with
phase `p`, so it never meets a state of another phase. A same-phase target that the run avoids
up to its endpoint would also do, while a redirect back to the entry fails at time `0`; a
generalization could ask for that avoidance instead.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`): up to the phase's time the
host is the phase run tagged with `p`, and one dispatch step later it is the phase's endpoint
with its state bound through `red p`. This gives the run, and the exit is the target of the
phase's live exit. For the cut, a time up to the phase's time carries a state tagged with `p`,
or `none`; a target equal to it would lie in phase `p`, against `q.1 ≠ p`. The envelope is the
phase's up to its time; at the dispatch step the heads are those of the phase's endpoint. -/
def inPhase {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i)) (q0 : Σ i, Ph i)
    (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p} {X : Set (Option (Ph p))}
    {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x) (hnone : none ∉ X)
    (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    Contract (phaseHostTM Mf q0 red) ⟨p, s₀⟩ {q | ∃ s, some s ∈ X ∧ q = red p s} ι x where
  pre i d := C.pre i (d.mapState fun _ => s₀)
  time i d := C.time i (d.mapState fun _ => s₀) + 1
  post i d := (C.post i (d.mapState fun _ => s₀)).bindState (red p)
  lo i d := C.lo i (d.mapState fun _ => s₀)
  hi i d := C.hi i (d.mapState fun _ => s₀)
  run i d hd hp := (inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp).2.1
  exit_mem i d hd hp := by
    obtain ⟨-, -, s', hs', hs'X⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    refine ⟨s', hs'X, ?_⟩
    show (C.post i (d.mapState fun _ => s₀)).state.bind (red p) = red p s'
    rw [hs']
    rfl
  cut i d hd hp u hu := by
    change u < C.time i (d.mapState fun _ => s₀) + 1 at hu
    obtain ⟨hL, -, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rw [hL u (by omega)]
    rintro ⟨s, hsX, heq⟩
    obtain ⟨q, hq, hqp⟩ := hsome s hsX
    rw [hq, mapState_state] at heq
    obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp heq
    exact hqp (by rw [← ha])
  env i d hd hp u hu j := by
    change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
    have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
    obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
    rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h | h
    · rw [hL u (by omega)]
      exact C.env i _ hc hp u (by omega) j
    · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
      rw [hE]
      have h' := C.env i _ hc hp _ le_rfl j
      rw [C.run i _ hc hp] at h'
      exact h'

end Compose

/-! ## The two-way branch -/

/-- The two-way composed start is the doubly left-mapped first-phase start. -/
private lemma mapState_const_inl_inl {S₀ S₁ S₂ : Type} {x : List Γ} {e : S₀}
    {d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x} (hd : d.state = some (Sum.inl (Sum.inl e))) :
    ((d.mapState fun _ => e).mapState (Sum.inl : S₀ → S₀ ⊕ S₁)).mapState
      (Sum.inl : S₀ ⊕ S₁ → (S₀ ⊕ S₁) ⊕ S₂) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- The two-way seam trajectory of a contract run: the doubly left-mapped first phase up to
its exit (live throughout), then, per exit, the matching continuation at every offset.

**Proof sketch.** The two-way seam nests two seams: the inner one dispatches `e₁` to the first
continuation, and the outer one dispatches the inner machine's `Sum.inl e₂` to the second.
`C₀`'s cut excludes both exits before its time. By the inner seam's left segment
(`Turing.seamCompTM_runFrom_left`), the inner machine therefore avoids `Sum.inl e₂` before that
time, so the outer seam's left segment, rewritten by the inner one, is the doubly tagged first
phase up to its time. It is live, since a halt would persist to the endpoint, which is at an
exit. The two continuations are the two halves of `Turing.seamCompTM₂_run_ofCfg`. -/
private lemma branch_traj {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} (M₁ : MultiTapeTM k Γ S₁) (M₂ : MultiTapeTM k Γ S₂)
    {entry₀ e₁ e₂ : S₀} (entry₁ : S₁) (entry₂ : S₂) {ι : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (i : ι)
    (d : Cfg k Γ ((S₀ ⊕ S₁) ⊕ S₂) x) (hd : d.state = some (Sum.inl (Sum.inl entry₀)))
    (hp : C₀.pre i (d.mapState fun _ => entry₀)) :
    (∀ u ≤ C₀.time i (d.mapState fun _ => entry₀),
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d u =
          ((M₀.runFrom (d.mapState fun _ => entry₀) u).mapState Sum.inl).mapState Sum.inl ∧
        (M₀.runFrom (d.mapState fun _ => entry₀) u).state ≠ none) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        ((M₁.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
          v).mapState Sum.inr).mapState Sum.inl) ∧
    ((C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ → ∀ v,
      (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂).runFrom d
          (C₀.time i (d.mapState fun _ => entry₀) + 1 + v) =
        (M₂.runFrom ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
          v).mapState Sum.inr) := by
  have hd' := mapState_const_inl_inl (S₁ := S₁) (S₂ := S₂) hd
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  have h0 := C₀.run i _ hc hp
  have hx := C₀.exit_mem i _ hc hp
  have hcut₁ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₁ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert _ _)
  have hcut₂ : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      (M₀.runFrom (d.mapState fun _ => entry₀) t).state ≠ some e₂ :=
    fun t ht h => C₀.cut i _ hc hp t ht (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
  have hcutO : ∀ t < C₀.time i (d.mapState fun _ => entry₀),
      ((seamCompTM M₀ e₁ M₁ entry₁).runFrom ((d.mapState fun _ => entry₀).mapState Sum.inl)
        t).state ≠ some (Sum.inl e₂) := by
    intro t ht h
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ t ht.le] at h
    exact hcut₂ t ht (by simpa [Cfg.mapState] using h)
  have H := seamCompTM₂_run_ofCfg M₀ e₁ e₂ he M₁ entry₁ M₂ entry₂ h0
    (fun t ht => ⟨hcut₁ t ht, hcut₂ t ht⟩)
  rw [hd'] at H
  refine ⟨fun u hu => ⟨?_, ?_⟩, H.1, H.2⟩
  · have h := seamCompTM_runFrom_left (seamCompTM M₀ e₁ M₁ entry₁) (Sum.inl e₂) M₂ entry₂
      hcutO u hu
    rw [seamCompTM_runFrom_left M₀ e₁ M₁ entry₁ hcut₁ u hu, hd'] at h
    exact h
  · refine MultiTapeTM.runFrom_state_ne_none_of_le M₀ _ _ ?_ u hu
    rw [h0]
    intro h'
    rw [h'] at hx
    simp at hx

/-- **The two-way branch** (`Turing.seamCompTM₂_run_ofCfg`): the first phase ends at one of two
distinct live exits, and the seam dispatches, in one step, to the matching continuation, which
starts from the first phase's endpoint with its state replaced by its entry. Each
continuation's precondition is needed only when its exit is the one reached. The time, the
endpoint and the continuation part of the envelope hull are the selected continuation's.

This is the **binary case** of the routing: `Turing.Contract.seq` is the single-live-exit seam,
and the phase host (`Turing.Contract.inPhase`) handles an arbitrary set of live exits. Halted
endpoints of the two continuations share the untagged `none`, so a consumer that must recover
the branch from the final state needs live tagged exits or an explicit verdict.

**Proof sketch.** By the two-way trajectory (`branch_traj`), and by cases on the exit reached
(`e₁`, or else `e₂` by `exit_mem`). Up to the first phase's time the composite is the doubly
left-tagged first phase, live throughout, so it meets no exit of either continuation. At time
`t₀ + 1 + v` it is the selected continuation's run at `v`, tagged, which gives the run, the exit
and the envelope. For the cut at `v` below the continuation's time, a tagged exit of the
selected continuation is excluded by that continuation's cut, through injectivity of the tags;
an exit of the other continuation carries the other tag or is `none`, and the state is live by
`Turing.Contract.live`. -/
def branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁] {M₀ : MultiTapeTM k Γ S₀}
    {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂} {entry₀ e₁ e₂ : S₀} {entry₁ : S₁}
    {entry₂ : S₂} {X₁ : Set (Option S₁)} {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ}
    (he : e₁ ≠ e₂) (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x)
    (C₁ : Contract M₁ entry₁ X₁ κ₁ x) (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁)
    (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    Contract (seamCompTM₂ M₀ e₁ e₂ M₁ entry₁ M₂ entry₂) (Sum.inl (Sum.inl entry₀))
      ((Option.map (Sum.inl ∘ Sum.inr) '' X₁) ∪ (Option.map Sum.inr '' X₂)) ι x where
  pre i d := C₀.pre i (d.mapState fun _ => entry₀)
  time i d :=
    C₀.time i (d.mapState fun _ => entry₀) + 1 +
      if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
        C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)
      else C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)
  post i d :=
    if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      ((C₁.post (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁)).mapState
        Sum.inr).mapState Sum.inl
    else
      (C₂.post (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂)).mapState
        Sum.inr
  lo i d j := min (C₀.lo i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.lo (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.lo (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  hi i d j := max (C₀.hi i (d.mapState fun _ => entry₀) j)
    (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
      C₁.hi (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) j
    else C₂.hi (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) j)
  run i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨-, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h, if_pos h, H₁ h, C₁.run _ _ hd₁ (h₁ i _ hc hp h)]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h, if_neg h, H₂ h', C₂.run _ _ hd₂ (h₂ i _ hc hp h')]
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      rw [if_pos h]
      refine Or.inl ⟨_, C₁.exit_mem _ _ hd₁ (h₁ i _ hc hp h), ?_⟩
      rw [mapState_state, mapState_state, Option.map_map]
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      rw [if_neg h]
      exact Or.inr ⟨_, C₂.exit_mem _ _ hd₂ (h₂ i _ hc hp h'), rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · obtain ⟨hrun, hlive⟩ := HL u hle
      rw [hrun]
      obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
      rintro (⟨q, -, heq⟩ | ⟨q, -, heq⟩) <;>
        rw [mapState_state, mapState_state, hs] at heq <;> cases q <;> simp at heq
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        have hv : v < C₁.time (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₁) := by omega
        have hcut := C₁.cut _ _ hd₁ (h₁ i _ hc hp h) v hv
        have hlive := live C₁ _ _ hd₁ (h₁ i _ hc hp h) hv
        rw [H₁ h v]
        rintro (⟨q, hq, heq⟩ | ⟨q, -, heq⟩)
        · rw [mapState_state, mapState_state, Option.map_map] at heq
          exact hcut (Option.map_injective (Sum.inl_injective.comp Sum.inr_injective) heq ▸ hq)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, mapState_state, hs] at heq
          cases q <;> simp at heq
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        have hv : v < C₂.time (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState
            fun _ => entry₂) := by omega
        have hcut := C₂.cut _ _ hd₂ (h₂ i _ hc hp h') v hv
        have hlive := live C₂ _ _ hd₂ (h₂ i _ hc hp h') hv
        rw [H₂ h' v]
        rintro (⟨q, -, heq⟩ | ⟨q, hq, heq⟩)
        · obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hlive
          rw [mapState_state, hs] at heq
          cases q <;> simp at heq
        · rw [mapState_state] at heq
          exact hcut (Option.map_injective Sum.inr_injective heq ▸ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
    obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
    by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
    · rw [(HL u hle).1]
      exact Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _) (C₀.env i _ hc hp u hle j)
    · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
        ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
      by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
      · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
            some entry₁ := by rw [mapState_state, h]; rfl
        rw [if_pos h] at hu
        rw [if_pos h, if_pos h, H₁ h v]
        exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
          (C₁.env _ _ hd₁ (h₁ i _ hc hp h) v (by omega) j)
      · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
          rcases C₀.exit_mem i _ hc hp with h'' | h''
          · exact absurd h'' h
          · exact h''
        have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
            some entry₂ := by rw [mapState_state, h']; rfl
        rw [if_neg h] at hu
        rw [if_neg h, if_neg h, H₂ h' v]
        exact Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)
          (C₂.env _ _ hd₂ (h₂ i _ hc hp h') v (by omega) j)

/-! ### The specification API (user, 2026-10-16)

The data fields of the seam, phase and branch composites as equations, generated by `simps`
without the `simp` attribute, so that consumers never unfold the definitions. -/

attribute [simps (config := { isSimp := false }) pre time post lo hi] seq inPhase branch

end Contract

/-! ## The release adapter -/

/-- The release start is the anchor-mapped start, re-tagged fresh. -/
private lemma release_start {S : Type} {anchor : S} {x : List Γ} {d : Cfg k Γ (Unit ⊕ S) x}
    (hd : d.state = some (Sum.inl ())) :
    (d.mapState fun _ => anchor).mapState (fun _ => (Sum.inl () : Unit ⊕ S)) = d :=
  Cfg.ext (by simp [Cfg.mapState, hd]) rfl rfl rfl rfl

/-- **The release adapter** (`Turing.seamReleaseTM_firstReturn`): a fresh start state executes the
anchor's first step, so the returning run becomes an ordinary contract whose cut includes time
`0`, at the same time and with no dispatch step. Its single exit is the right-tagged anchor, and
the envelopes are unchanged.

**Proof sketch.** The release start is the anchor-mapped start re-tagged fresh
(`release_start`). Fed the returning contract's positivity, run, return and positive cut,
`Turing.seamReleaseTM_firstReturn` gives the run to the right-tagged endpoint at the same time,
and the cut against the right-tagged anchor at every earlier time, time `0` included since the
fresh state is left-tagged. The exit is the endpoint's state, the anchor, right-tagged. For the
envelope, the head vector at time `0` is the start's; at a positive time the release run is
the source run, right-tagged (`Turing.seamReleaseTM_runFrom_pos`), so its heads are the
source's, inside the source envelope. -/
def ReturnContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {ι : Type}
    {x : List Γ} (C : ReturnContract M anchor ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ()) {some (Sum.inr anchor)} ι x where
  pre i d := C.pre i (d.mapState fun _ => anchor)
  time i d := C.time i (d.mapState fun _ => anchor)
  post i d := (C.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := C.lo i (d.mapState fun _ => anchor)
  hi i d := C.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.1
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    show Option.map Sum.inr (C.post i (d.mapState fun _ => anchor)).state ∈ _
    rw [C.exit_eq i _ hc hp]
    rfl
  cut i d hd hp u hu hmem := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_firstReturn M anchor hc (C.pos i _ hc hp) (C.run i _ hc hp)
      (C.exit_eq i _ hc hp) (C.cut i _ hc hp)
    rw [release_start hd] at H
    exact H.2 u hu (Set.mem_singleton_iff.mp hmem)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · have h0 := C.env i _ hc hp 0 (Nat.zero_le _) j
      rw [MultiTapeTM.runFrom_zero] at h0 ⊢
      exact h0
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H]
      exact C.env i _ hc hp u hu j

/-- **The round release** (design §16a item 2, with item 5's export): a fresh start state
executes the anchor's first step, so a round becomes an ordinary contract whose exits are the
right-tagged images of the anchor and of the escape set, at the same time and with the same
envelope. The escape set is arbitrary: it may contain `none` (a round that halts still ends
halted, since the tag keeps `none`), several states, or the anchor itself. **Only for a single
live escape distinct from the anchor**, `escape = {some e}` with `e ≠ anchor`, are the exits two
distinct live states, `some (Sum.inr anchor)` and `some (Sum.inr e)`, the shape of
`Turing.Contract.branch`'s first phase. Routing through the phase host
(`Turing.Contract.inPhase`) needs in general that `none` is not an exit and the redirect
conditions.

**Proof sketch.** At every positive time the release run is the round run, right-tagged
(`Turing.seamReleaseTM_runFrom_pos`), and the release start re-tags the anchor-mapped start. The
run and the exit are the round's, tagged. The cut at time `0` holds since the fresh state is
left-tagged; at a positive time a tagged exit would be an anchor or escape state of the round
before its end, which its cut excludes. The heads are the round's at every time. -/
def RoundContract.release {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {escape : Set (Option S)} {ι : Type} {x : List Γ} (R : RoundContract M anchor escape ι x) :
    Contract (seamReleaseTM M anchor) (Sum.inl ())
      (Option.map Sum.inr '' insert (some anchor) escape) ι x where
  pre i d := R.pre i (d.mapState fun _ => anchor)
  time i d := R.time i (d.mapState fun _ => anchor)
  post i d := (R.post i (d.mapState fun _ => anchor)).mapState Sum.inr
  lo i d := R.lo i (d.mapState fun _ => anchor)
  hi i d := R.hi i (d.mapState fun _ => anchor)
  run i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    have H := seamReleaseTM_runFrom_pos M anchor _ hc _ (R.pos i _ hc hp)
    rw [release_start hd, R.run i _ hc hp] at H
    exact H
  exit_mem i d hd hp := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    exact ⟨_, R.exit_mem i _ hc hp, rfl⟩
  cut i d hd hp u hu := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rintro ⟨q, hq, heq⟩
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · rw [MultiTapeTM.runFrom_zero, hd] at heq
      cases q <;> simp at heq
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H] at heq
      have hq' : q = (M.runFrom (d.mapState fun _ => anchor) u).state :=
        Option.map_injective Sum.inr_injective heq
      exact R.cut i _ hc hp u hpos hu (hq' ▸ Set.mem_insert_of_mem _ hq)
  env i d hd hp u hu j := by
    have hc : (d.mapState fun _ => anchor).state = some anchor := by simp [Cfg.mapState, hd]
    rcases Nat.eq_zero_or_pos u with rfl | hpos
    · have h0 := R.env i _ hc hp 0 (Nat.zero_le _) j
      rw [MultiTapeTM.runFrom_zero] at h0 ⊢
      exact h0
    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos
      rw [release_start hd] at H
      rw [H]
      exact R.env i _ hc hp u hu j

/-! The specification API (user, 2026-10-16; its gate, finding 1): the two release adapters'
data fields as equations, generated by `simps` without the `simp` attribute, so that consumers
never unfold the definitions. -/
attribute [simps (config := { isSimp := false }) pre time post lo hi]
  ReturnContract.release RoundContract.release

/-! ## Joint trajectories, frames and positivity of the seam compositions (MIG-0b) -/

namespace Contract

/-- **`seq` preserves joint trajectories**: the first relation through the first phase, and the
second from the dispatch on (the dispatch step is stationary, so it is the second phase's time
`0`).

**Proof sketch.** By the seam trajectory (`seq_traj`), split at the first phase's time, as in
`Turing.Contract.seq`'s envelope. -/
theorem Traj.seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} {C₁ : Contract M₁ entry₁ {some exit₁} ι x}
    {C₂ : Contract M₂ entry₂ X₂ κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)}
    {R₁ : ι → Cfg k Γ S₁ x → (Fin k → ℤ) → Prop} {R₂ : κ → Cfg k Γ S₂ x → (Fin k → ℤ) → Prop}
    (h₁ : C₁.Traj R₁) (h₂ : C₂.Traj R₂) :
    (C₁.seq C₂ link hlink).Traj fun i d p => R₁ i (d.mapState fun _ => entry₁) p ∨
      R₂ (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) p := by
  intro i d hd hp u hu
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  obtain ⟨hL, hR, hd₂⟩ := seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp
  change u ≤ C₁.time i (d.mapState fun _ => entry₁) + 1 +
    C₂.time (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) at hu
  by_cases hle : u ≤ C₁.time i (d.mapState fun _ => entry₁)
  · rw [(hL u hle).1]
    exact Or.inl (h₁ i _ hd₁ hp u hle)
  · obtain ⟨v, rfl⟩ : ∃ v, u = C₁.time i (d.mapState fun _ => entry₁) + 1 + v :=
      ⟨u - (C₁.time i (d.mapState fun _ => entry₁) + 1), by omega⟩
    rw [hR v]
    exact Or.inr (h₂ _ _ hd₂ (hlink i _ hd₁ hp) v (by omega))

/-- **`seq` preserves frames**: the first footprint at the first-phase start and the second at
the second-phase start. Frames ignore control states, so the seam's tags do not matter.

**Proof sketch.** The first phase frames the start against its endpoint, and the second its
start, the state-replaced first endpoint, against the second endpoint; compose
(`Turing.Cfg.SameOutside.trans`) and re-tag (`Turing.Cfg.SameOutside.mapState`). -/
theorem Frames.seq {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} {C₁ : Contract M₁ entry₁ {some exit₁} ι x}
    {C₂ : Contract M₂ entry₂ X₂ κ x} {link : ι → κ}
    {hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)}
    {fp₁ : ι → Cfg k Γ S₁ x → Fin k → Set ℤ} {fp₂ : κ → Cfg k Γ S₂ x → Fin k → Set ℤ}
    (h₁ : C₁.Frames fp₁) (h₂ : C₂.Frames fp₂) :
    (C₁.seq C₂ link hlink).Frames fun i d j => fp₁ i (d.mapState fun _ => entry₁) j ∪
      fp₂ (link i) ((C₁.post i (d.mapState fun _ => entry₁)).mapState fun _ => entry₂) j := by
  intro i d hd hp
  have hd₁ : (d.mapState fun _ => entry₁).state = some entry₁ := by simp [Cfg.mapState, hd]
  have hd₂ := (seq_traj (M₂ := M₂) entry₂ C₁ i d hd hp).2.2
  have f₁ : Cfg.SameOutside (fp₁ i (d.mapState fun _ => entry₁)) d
      (C₁.post i (d.mapState fun _ => entry₁)) := h₁ i _ hd₁ hp
  have f₂ := h₂ _ _ hd₂ (hlink i _ hd₁ hp)
  exact (f₁.trans fun j q hq => f₂ j q hq).mapState Sum.inr

/-- **`inPhase` preserves joint trajectories**: the phase's relation, at the state-replaced start.
The dispatch step is stationary.

**Proof sketch.** By the phase-host trajectory (`inPhase_traj`), as in
`Turing.Contract.inPhase`'s envelope: up to the phase's time the host heads are the phase's, and
at the dispatch they are the phase endpoint's. -/
theorem Traj.inPhase {I : Type} {Ph : I → Type} {Mf : (i : I) → MultiTapeTM k Γ (Ph i)}
    {q0 : Σ i, Ph i} {red : (i : I) → Ph i → Option (Σ i, Ph i)} {p : I} {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} {C : Contract (Mf p) s₀ X ι x}
    {hnone : none ∉ X} {hred : ∀ s, some s ∉ X → red p s = none}
    {hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p}
    {R : ι → Cfg k Γ (Ph p) x → (Fin k → ℤ) → Prop} (h : C.Traj R) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).Traj
      fun i d => R i (d.mapState fun _ => s₀) := by
  intro i d hd hp u hu
  change u ≤ C.time i (d.mapState fun _ => s₀) + 1 at hu
  have hc : (d.mapState fun _ => s₀).state = some s₀ := by simp [Cfg.mapState, hd]
  obtain ⟨hL, hE, -⟩ := inPhase_traj Mf q0 red p C hnone hred hsome i d hd hp
  rcases Nat.lt_or_ge u (C.time i (d.mapState fun _ => s₀) + 1) with h' | h'
  · rw [hL u (by omega)]
    exact h i _ hc hp u (by omega)
  · obtain rfl : u = C.time i (d.mapState fun _ => s₀) + 1 := by omega
    rw [hE]
    have h'' := h i _ hc hp _ le_rfl
    rw [C.run i _ hc hp] at h''
    exact h''

/-- **`branch` preserves joint trajectories**: the first phase's relation up to its time, then
the relation of the continuation that its exit selects.

**Proof sketch.** By the two-way trajectory (`branch_traj`) and by cases on the exit reached, as
in `Turing.Contract.branch`'s envelope. -/
theorem Traj.branch {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)}
    {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ} {he : e₁ ≠ e₂}
    {C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x} {C₁ : Contract M₁ entry₁ X₁ κ₁ x}
    {C₂ : Contract M₂ entry₂ X₂ κ₂ x} {l₁ : ι → κ₁} {l₂ : ι → κ₂}
    {h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁)}
    {h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)}
    {R₀ : ι → Cfg k Γ S₀ x → (Fin k → ℤ) → Prop} {R₁ : κ₁ → Cfg k Γ S₁ x → (Fin k → ℤ) → Prop}
    {R₂ : κ₂ → Cfg k Γ S₂ x → (Fin k → ℤ) → Prop}
    (t₀ : C₀.Traj R₀) (t₁ : C₁.Traj R₁) (t₂ : C₂.Traj R₂) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).Traj fun i d p =>
      R₀ i (d.mapState fun _ => entry₀) p ∨
        (if (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁ then
          R₁ (l₁ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁) p
        else
          R₂ (l₂ i) ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂) p) := by
  intro i d hd hp u hu
  have hc : (d.mapState fun _ => entry₀).state = some entry₀ := by simp [Cfg.mapState, hd]
  obtain ⟨HL, H₁, H₂⟩ := branch_traj M₁ M₂ entry₁ entry₂ he C₀ i d hd hp
  by_cases hle : u ≤ C₀.time i (d.mapState fun _ => entry₀)
  · rw [(HL u hle).1]
    exact Or.inl (t₀ i _ hc hp u hle)
  · obtain ⟨v, rfl⟩ : ∃ v, u = C₀.time i (d.mapState fun _ => entry₀) + 1 + v :=
      ⟨u - (C₀.time i (d.mapState fun _ => entry₀) + 1), by omega⟩
    right
    by_cases h : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₁
    · have hd₁ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₁).state =
          some entry₁ := by rw [mapState_state, h]; rfl
      change _ ≤ _ + 1 + (if _ then _ else _) at hu
      rw [if_pos h] at hu
      rw [if_pos h, H₁ h v]
      exact t₁ _ _ hd₁ (h₁ i _ hc hp h) v (by omega)
    · have h' : (C₀.post i (d.mapState fun _ => entry₀)).state = some e₂ := by
        rcases C₀.exit_mem i _ hc hp with h'' | h''
        · exact absurd h'' h
        · exact h''
      have hd₂ : ((C₀.post i (d.mapState fun _ => entry₀)).mapState fun _ => entry₂).state =
          some entry₂ := by rw [mapState_state, h']; rfl
      change _ ≤ _ + 1 + (if _ then _ else _) at hu
      rw [if_neg h] at hu
      rw [if_neg h, H₂ h' v]
      exact t₂ _ _ hd₂ (h₂ i _ hc hp h') v (by omega)

/-- `seq` is positive: it takes a dispatch step. -/
theorem seq_positive {S₁ S₂ : Type} [DecidableEq S₁] {M₁ : MultiTapeTM k Γ S₁}
    {M₂ : MultiTapeTM k Γ S₂} {entry₁ exit₁ : S₁} {entry₂ : S₂} {X₂ : Set (Option S₂)}
    {ι κ : Type} {x : List Γ} (C₁ : Contract M₁ entry₁ {some exit₁} ι x)
    (C₂ : Contract M₂ entry₂ X₂ κ x) (link : ι → κ)
    (hlink : ∀ i d, d.state = some entry₁ → C₁.pre i d →
      C₂.pre (link i) ((C₁.post i d).mapState fun _ => entry₂)) :
    (C₁.seq C₂ link hlink).Positive :=
  fun _ _ _ _ => Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

/-- `inPhase` is positive: it takes a dispatch step. -/
theorem inPhase_positive {I : Type} {Ph : I → Type} (Mf : (i : I) → MultiTapeTM k Γ (Ph i))
    (q0 : Σ i, Ph i) (red : (i : I) → Ph i → Option (Σ i, Ph i)) (p : I) {s₀ : Ph p}
    {X : Set (Option (Ph p))} {ι : Type} {x : List Γ} (C : Contract (Mf p) s₀ X ι x)
    (hnone : none ∉ X) (hred : ∀ s, some s ∉ X → red p s = none)
    (hsome : ∀ s, some s ∈ X → ∃ q, red p s = some q ∧ q.1 ≠ p) :
    (Contract.inPhase Mf q0 red p C hnone hred hsome).Positive :=
  fun _ _ _ _ => Nat.succ_pos _

/-- `branch` is positive: it takes a dispatch step. -/
theorem branch_positive {S₀ S₁ S₂ : Type} [DecidableEq S₀] [DecidableEq S₁]
    {M₀ : MultiTapeTM k Γ S₀} {M₁ : MultiTapeTM k Γ S₁} {M₂ : MultiTapeTM k Γ S₂}
    {entry₀ e₁ e₂ : S₀} {entry₁ : S₁} {entry₂ : S₂} {X₁ : Set (Option S₁)}
    {X₂ : Set (Option S₂)} {ι κ₁ κ₂ : Type} {x : List Γ} (he : e₁ ≠ e₂)
    (C₀ : Contract M₀ entry₀ {some e₁, some e₂} ι x) (C₁ : Contract M₁ entry₁ X₁ κ₁ x)
    (C₂ : Contract M₂ entry₂ X₂ κ₂ x) (l₁ : ι → κ₁) (l₂ : ι → κ₂)
    (h₁ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₁ →
      C₁.pre (l₁ i) ((C₀.post i d).mapState fun _ => entry₁))
    (h₂ : ∀ i d, d.state = some entry₀ → C₀.pre i d → (C₀.post i d).state = some e₂ →
      C₂.pre (l₂ i) ((C₀.post i d).mapState fun _ => entry₂)) :
    (Contract.branch he C₀ C₁ C₂ l₁ l₂ h₁ h₂).Positive :=
  fun _ _ _ _ => Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_add_right _ _)

end Contract

/-- The release of a returning contract is positive, since a return takes positive time. -/
theorem ReturnContract.release_positive {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {ι : Type} {x : List Γ} (C : ReturnContract M anchor ι x) : C.release.Positive :=
  fun i d hd hp => C.pos i _ (by simp [Cfg.mapState, hd]) hp

/-- The release of a round contract is positive, since a round takes positive time. -/
theorem RoundContract.release_positive {S : Type} {M : MultiTapeTM k Γ S} {anchor : S}
    {escape : Set (Option S)} {ι : Type} {x : List Γ} (R : RoundContract M anchor escape ι x) :
    R.release.Positive :=
  fun i d hd hp => R.pos i _ (by simp [Cfg.mapState, hd]) hp

end Turing
