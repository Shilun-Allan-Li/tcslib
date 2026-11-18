/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.TuringMachine.Build.Contract.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Reaching an endpoint within bounds

Many rows of the construction layer are stated existentially: from a configuration satisfying a
precondition, the machine reaches a stated endpoint at some time within a bound, with no exit
earlier and every head within a radius. `Turing.ReachesWithin` names that shape once, and
`Turing.Contract.ofReaches` turns a row in that shape into a `Turing.Contract`, choosing the time,
so that existential rows compose with `Turing.Contract.seq`, `inPhase` and `branch`.

## Main definitions

* `Turing.ReachesWithin`: the endpoint is reached within `B` steps, no state of `X` earlier, every
  head within `E` cells of its start.
* `Turing.Contract.ofReaches`: the contract of a row stated with `ReachesWithin`.

## Main results

* `Turing.reachesWithin_iff`, `Turing.ReachesWithin.mono`.
* `Turing.Contract.ofReaches_time_le`, and the field equations of `Contract.ofReaches`.

## References

* [AFM26] Anthropic, PBC, `anthropics/formal-math`, project `3sum-apsp`, commit `e1a4e650`,
  Apache-2.0: the framing adapted as `Turing.Contract` (design adaptation; full entry in
  `Build/Contract/Basic`).
-/

namespace Turing

variable {k : ℕ} {Γ : Type}

/-- **Reaching an endpoint within bounds.** `ReachesWithin M d X B E post`: run from `d`, the
machine `M` is at `post` at some time `t ≤ B`; at every earlier time its state is not in `X`; and
at every time up to `t` each work head is within `E` cells of where it was in `d`. -/
def ReachesWithin {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (d : Cfg k Γ S x)
    (X : Set (Option S)) (B E : ℕ) (post : Cfg k Γ S x) : Prop :=
  ∃ t ≤ B, (∀ s < t, (M.runFrom d s).state ∉ X) ∧
    (∀ s ≤ t, ∀ j : Fin k, |(M.runFrom d s).workTapePos j - d.workTapePos j| ≤ (E : ℤ)) ∧
    M.runFrom d t = post

/-- `ReachesWithin`, as an equivalence with its definition. -/
theorem reachesWithin_iff {S : Type} {x : List Γ} (M : MultiTapeTM k Γ S) (d : Cfg k Γ S x)
    (X : Set (Option S)) (B E : ℕ) (post : Cfg k Γ S x) :
    ReachesWithin M d X B E post ↔
      ∃ t ≤ B, (∀ s < t, (M.runFrom d s).state ∉ X) ∧
        (∀ s ≤ t, ∀ j : Fin k, |(M.runFrom d s).workTapePos j - d.workTapePos j| ≤ (E : ℤ)) ∧
        M.runFrom d t = post :=
  Iff.rfl

/-- Larger bounds: an endpoint reached within `B` steps and radius `E` is reached within any
`B' ≥ B` and `E' ≥ E`. -/
theorem ReachesWithin.mono {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {d : Cfg k Γ S x}
    {X : Set (Option S)} {B E B' E' : ℕ} {post : Cfg k Γ S x}
    (h : ReachesWithin M d X B E post) (hB : B ≤ B') (hE : E ≤ E') :
    ReachesWithin M d X B' E' post := by
  obtain ⟨t, ht, hcut, henv, hrun⟩ := h
  exact ⟨t, ht.trans hB, hcut, fun s hs j => (henv s hs j).trans (by exact_mod_cast hE), hrun⟩

/-- **The contract of a row stated with `ReachesWithin`.** If from the entry, under `pre`, the
machine reaches `post` within `B` steps and radius `E`, with no state of `X` earlier, and the
endpoint's state lies in `X`, then this is the contract with that precondition and endpoint, the
exits `X`, the time chosen from the row (`0` off the precondition), and the head intervals
`[pos - E, pos + E]`.

**Proof sketch.** Under the precondition the time is the chosen witness, so the run, the cut and
the envelope are the row's clauses, the envelope read through `abs_le`; the exit is `hX`. -/
noncomputable def Contract.ofReaches {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} (pre : ι → Cfg k Γ S x → Prop)
    (B E : ι → Cfg k Γ S x → ℕ) (post : ι → Cfg k Γ S x → Cfg k Γ S x)
    (h : ∀ i d, d.state = some entry → pre i d → ReachesWithin M d X (B i d) (E i d) (post i d))
    (hX : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ X) :
    Contract M entry X ι x where
  pre := pre
  time i d := haveI := Classical.propDecidable (d.state = some entry ∧ pre i d)
    if hd : d.state = some entry ∧ pre i d then Classical.choose (h i d hd.1 hd.2) else 0
  post := post
  lo i d j := d.workTapePos j - E i d
  hi i d j := d.workTapePos j + E i d
  run i d hd hp := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)]
    exact (Classical.choose_spec (h i d hd hp)).2.2.2
  exit_mem i d hd hp := hX i d hd hp
  cut i d hd hp u hu := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)] at hu
    exact (Classical.choose_spec (h i d hd hp)).2.1 u hu
  env i d hd hp u hu j := by
    simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)] at hu
    have := (Classical.choose_spec (h i d hd hp)).2.2.1 u hu j
    rw [abs_le] at this
    exact Finset.mem_Icc.mpr ⟨by linarith, by linarith⟩

/-- The contract of a row stated with `ReachesWithin` takes at most the row's bound.

**Proof sketch.** Under the precondition the time is the chosen witness, which is at most `B`. -/
theorem Contract.ofReaches_time_le {S : Type} {M : MultiTapeTM k Γ S} {entry : S}
    {X : Set (Option S)} {ι : Type} {x : List Γ} (pre : ι → Cfg k Γ S x → Prop)
    (B E : ι → Cfg k Γ S x → ℕ) (post : ι → Cfg k Γ S x → Cfg k Γ S x)
    (h : ∀ i d, d.state = some entry → pre i d → ReachesWithin M d X (B i d) (E i d) (post i d))
    (hX : ∀ i d, d.state = some entry → pre i d → (post i d).state ∈ X) (i : ι)
    (d : Cfg k Γ S x) (hd : d.state = some entry) (hp : pre i d) :
    (Contract.ofReaches pre B E post h hX).time i d ≤ B i d := by
  show (haveI := Classical.propDecidable (d.state = some entry ∧ pre i d)
    if hd : d.state = some entry ∧ pre i d then Classical.choose (h i d hd.1 hd.2) else 0) ≤ B i d
  simp only [dif_pos (show d.state = some entry ∧ pre i d from ⟨hd, hp⟩)]
  exact (Classical.choose_spec (h i d hd hp)).1

attribute [simps (config := { isSimp := false }) pre post lo hi] Contract.ofReaches

end Turing
