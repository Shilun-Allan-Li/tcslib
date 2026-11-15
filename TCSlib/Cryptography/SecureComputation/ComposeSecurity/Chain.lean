/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Probability
import TCSlib.Cryptography.Pseudorandom.Indistinguishability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The hybrid argument over the runs

Step 3 of the proof of the composition theorem [Gol04, §7.3.1, proof of Theorem 7.3.3], in a
generic form. A sample is `Φ m V`, built from a seed `m : M` and one word `V j` per run `j < L`.
In the real sample run `j` is `real m j x_j` for an independent seed `x_j : X`; in the simulated
sample it is `sim m j s_j` for an independent `s_j : S`. The hybrid `i` (`hybV`) takes the first
`i` runs simulated and the others real, on the joint seed `(m, (x_j, s_j)_j)`. Neighbouring
hybrids differ in run `i` only, and resampling that run's seeds (`exists_hyb_step`, with the
published `acceptProb_update`) bounds their gap by the gap at fixed other coordinates (`plugV`:
run `i` replaced by a given word). Summing (`abs_sub_le_sum_hybrids`) gives `abs_chain_le`.

## Main definitions

* `ComposeProb.hybV`: the run words of hybrid `i`; `ComposeProb.plugV`: with run `i` replaced.

## Main results

* `ComposeProb.exists_hyb_step`: one step of the hybrid argument.
* `ComposeProb.abs_chain_le`: the real and the simulated samples are within `L · g` when every
  step at fixed other coordinates is within `g`.
* `ComposeProb.getD_plug`: the word list of the reduction's template.

## References

* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*, Cambridge
  University Press, 2004, §7.3.1 (the proof of Theorem 7.3.3).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, §3.2 (hybrid arguments).
-/

namespace TCSlib.Cryptography.SecureComputation.ComposeProb

open Finset

section Chain

variable {M X S γ ρ : Type*} {L : ℕ}

/-- **The run words of hybrid `i`** on the seed `ω = (m, (x_j, s_j)_j)`: run `j < L` is
`sim m j s_j` for `j < i` and `real m j x_j` otherwise; `[]` for `j ≥ L`. -/
def hybV (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (ω : M × (Fin L → X × S)) (j : ℕ) : List Bool :=
  if h : j < L then
    (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
  else []

/-- The defining equation of `hybV` (see `hybV`).
`hybV real sim i ω j = if h : j < L then (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1
⟨j, h⟩ (ω.2 ⟨j, h⟩).1) else []`. -/
theorem hybV_eq (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (ω : M × (Fin L → X × S)) (j : ℕ) :
    hybV real sim i ω j =
      if h : j < L then
        (if j < i then sim ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).2 else real ω.1 ⟨j, h⟩ (ω.2 ⟨j, h⟩).1)
      else [] := rfl

/-- **Hybrid `i` with run `i` replaced by the word `v`**: `plugV real sim i a v j = v` for
`j = i` and `hybV real sim i a j` otherwise. -/
def plugV (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (a : M × (Fin L → X × S)) (v : List Bool) (j : ℕ) : List Bool :=
  if j = i then v else hybV real sim i a j

/-- The defining equation of `plugV` (see `plugV`).
`plugV real sim i a v j = if j = i then v else hybV real sim i a j`. -/
theorem plugV_eq (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool) (i : ℕ)
    (a : M × (Fin L → X × S)) (v : List Bool) (j : ℕ) :
    plugV real sim i a v j = if j = i then v else hybV real sim i a j := rfl

/-- Hybrid `i` with run `i` reseeded by `(x, s)` has the real run `i` on `x`:
`hybV i (m, update u i (x, s)) = plugV i (m, u) (real m i x)`. -/
theorem hybV_update (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (i : Fin L) (m : M) (u : Fin L → X × S) (y : X × S) :
    hybV real sim i (m, Function.update u i y) = plugV real sim i (m, u) (real m i y.1) := by
  funext j
  rw [hybV_eq, plugV_eq, hybV_eq]
  by_cases hji : j = i
  · subst hji
    rw [dif_pos i.2, if_neg (lt_irrefl _), if_pos rfl]
    simp only [Fin.eta, Function.update_self]
  · rw [if_neg hji]
    by_cases hj : j < L
    · have hne : (⟨j, hj⟩ : Fin L) ≠ i := fun h => hji (congrArg Fin.val h)
      rw [dif_pos hj, dif_pos hj]
      simp only [Function.update_of_ne hne]
    · rw [dif_neg hj, dif_neg hj]

/-- Hybrid `i + 1` with run `i` reseeded by `(x, s)` has the simulated run `i` on `s`:
`hybV (i + 1) (m, update u i (x, s)) = plugV i (m, u) (sim m i s)`. -/
theorem hybV_succ_update (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (i : Fin L) (m : M) (u : Fin L → X × S) (y : X × S) :
    hybV real sim ((i : ℕ) + 1) (m, Function.update u i y) =
      plugV real sim i (m, u) (sim m i y.2) := by
  funext j
  rw [hybV_eq, plugV_eq, hybV_eq]
  by_cases hji : j = i
  · subst hji
    rw [dif_pos i.2, if_pos (Nat.lt_succ_self _), if_pos rfl]
    simp only [Fin.eta, Function.update_self]
  · rw [if_neg hji]
    by_cases hj : j < L
    · have hne : (⟨j, hj⟩ : Fin L) ≠ i := fun h => hji (congrArg Fin.val h)
      have hlt : j < (i : ℕ) + 1 ↔ j < i := by omega
      rw [dif_pos hj, dif_pos hj]
      simp only [Function.update_of_ne hne, hlt]
    · rw [dif_neg hj, dif_neg hj]

variable [Fintype M] [Fintype X] [Fintype S] [Fintype ρ]

variable [Nonempty M] [Nonempty X] [Nonempty S]

/-- **One step of the hybrid argument**: for `i < L` there are fixed other coordinates `a` such
that the gap between hybrids `i` and `i + 1` is at most the gap between run `i` real and run `i`
simulated, the others as in `a`:
`|Pr[D(Φ(hyb i))] − Pr[D(Φ(hyb (i+1)))]| ≤
|Pr_x[D(Φ a.1 (plugV i a (real a.1 i x)))] − Pr_s[D(Φ a.1 (plugV i a (sim a.1 i s)))]|`.

**Proof sketch.** Overwrite run `i`'s seeds with a fresh `y : X × S` (`acceptProb_update`, after
moving `m` last and the fresh seed last, `acceptProb_comp_equiv`): hybrid `k` becomes
`hyb k (m, update u i y)`, which for `k = i` is the plugged real run on `y.1` and for `k = i + 1`
the plugged simulated run on `y.2` (`hybV_update`, `hybV_succ_update`). Fix the coordinates
`(u, m)` at the worst value (`exists_abs_sub_le_sections`) and drop the unused half of `y`
(`acceptProb_fst`, `acceptProb_snd`). -/
theorem exists_hyb_step (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) (i : Fin L) :
    ∃ a : M × (Fin L → X × S),
      |acceptProb (fun ω => Φ ω.1 (hybV real sim i ω)) D -
          acceptProb (fun ω => Φ ω.1 (hybV real sim ((i : ℕ) + 1) ω)) D| ≤
        |acceptProb (fun x => Φ a.1 (plugV real sim i a (real a.1 i x))) D -
          acceptProb (fun s => Φ a.1 (plugV real sim i a (sim a.1 i s))) D| := by
  classical
  -- overwrite run `i`'s seeds with a fresh seed; the fixed coordinates `(u, m)` come first
  have hk : ∀ k : ℕ, acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D =
      acceptProb (fun w : ((Fin L → X × S) × M) × (X × S) =>
        Φ w.1.2 (hybV real sim k (w.1.2, Function.update w.1.1 i w.2))) D := by
    intro k
    refine (acceptProb_comp_equiv (Equiv.prodComm (Fin L → X × S) M)
      (fun ω : M × (Fin L → X × S) => Φ ω.1 (hybV real sim k ω)) D).symm.trans ?_
    refine (acceptProb_update i (fun u m => Φ m (hybV real sim k (m, u))) D).symm.trans ?_
    exact (acceptProb_comp_equiv (Equiv.prodComm ((Fin L → X × S) × M) (X × S)) _ D).symm
  rw [hk i, hk ((i : ℕ) + 1)]
  obtain ⟨a, ha⟩ := exists_abs_sub_le_sections
    (fun w : ((Fin L → X × S) × M) × (X × S) =>
      Φ w.1.2 (hybV real sim i (w.1.2, Function.update w.1.1 i w.2)))
    (fun w : ((Fin L → X × S) × M) × (X × S) =>
      Φ w.1.2 (hybV real sim ((i : ℕ) + 1) (w.1.2, Function.update w.1.1 i w.2))) D
  refine ⟨(a.2, a.1), ha.trans (le_of_eq ?_)⟩
  simp only [hybV_update, hybV_succ_update]
  rw [acceptProb_fst (fun x => Φ a.2 (plugV real sim i (a.2, a.1) (real a.2 i x))) D,
    acceptProb_snd (fun s => Φ a.2 (plugV real sim i (a.2, a.1) (sim a.2 i s))) D]

omit [Nonempty M] [Nonempty X] in
/-- Hybrid `0` is the real sample, the simulator seeds unused:
`Pr[D(Φ(hyb 0))] = Pr_{(m, x)}[D(Φ m (real runs on x))]`. -/
theorem acceptProb_hyb_zero (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) :
    acceptProb (fun ω => Φ ω.1 (hybV real sim 0 ω)) D =
      acceptProb (fun z : M × (Fin L → X) =>
        Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D := by
  let e : M × (Fin L → X × S) ≃ (M × (Fin L → X)) × (Fin L → S) :=
    { toFun := fun ω => ((ω.1, fun j => (ω.2 j).1), fun j => (ω.2 j).2)
      invFun := fun z => (z.1.1, fun j => (z.1.2 j, z.2 j))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← acceptProb_fst (τ := Fin L → S) (fun z : M × (Fin L → X) =>
      Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D,
    ← acceptProb_comp_equiv e]
  congr 1

omit [Nonempty M] [Nonempty S] in
/-- Hybrid `L` is the simulated sample, the real seeds unused:
`Pr[D(Φ(hyb L))] = Pr_{(m, s)}[D(Φ m (simulated runs on s))]`.

**Proof sketch.** Relabel the seed `(m, (x_j, s_j)_j)` as `((m, s), x)` (an equivalence,
`acceptProb_comp_equiv`) and drop the unused `x` (`acceptProb_fst`); in hybrid `L` every
run `j < L` is simulated (`hybV_eq`). -/
theorem acceptProb_hyb_last (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) :
    acceptProb (fun ω => Φ ω.1 (hybV real sim L ω)) D =
      acceptProb (fun z : M × (Fin L → S) =>
        Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D := by
  let e : M × (Fin L → X × S) ≃ (M × (Fin L → S)) × (Fin L → X) :=
    { toFun := fun ω => ((ω.1, fun j => (ω.2 j).2), fun j => (ω.2 j).1)
      invFun := fun z => (z.1.1, fun j => (z.2 j, z.1.2 j))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← acceptProb_fst (τ := Fin L → X) (fun z : M × (Fin L → S) =>
      Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D,
    ← acceptProb_comp_equiv e]
  congr 1
  funext ω
  congr 1
  funext j
  rw [hybV_eq]
  by_cases h : j < L
  · rw [dif_pos h, dif_pos h, if_pos h]
    rfl
  · rw [dif_neg h, dif_neg h]

/-- **The hybrid argument over the runs**: if for every run `i < L` and all fixed other
coordinates `a` the plugged real and simulated runs are within `g`, then the real sample and the
simulated sample are within `L · g`:
`|Pr_{(m, x)}[D(Φ m (real runs))] − Pr_{(m, s)}[D(Φ m (simulated runs))]| ≤ L · g`.

**Proof sketch.** The two samples are hybrids `0` and `L` (`acceptProb_hyb_zero`,
`acceptProb_hyb_last`); telescope (`abs_sub_le_sum_hybrids`) and bound each of the `L` steps by
`g` (`exists_hyb_step`). -/
theorem abs_chain_le (real : M → Fin L → X → List Bool) (sim : M → Fin L → S → List Bool)
    (Φ : M → (ℕ → List Bool) → γ) (D : γ → ρ → Bool) (g : ℝ)
    (hg : ∀ (i : Fin L) (a : M × (Fin L → X × S)),
      |acceptProb (fun x => Φ a.1 (plugV real sim i a (real a.1 i x))) D -
        acceptProb (fun s => Φ a.1 (plugV real sim i a (sim a.1 i s))) D| ≤ g) :
    |acceptProb (fun z : M × (Fin L → X) =>
        Φ z.1 fun j => if h : j < L then real z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D -
      acceptProb (fun z : M × (Fin L → S) =>
        Φ z.1 fun j => if h : j < L then sim z.1 ⟨j, h⟩ (z.2 ⟨j, h⟩) else []) D| ≤ L * g := by
  have h0 := acceptProb_hyb_zero real sim Φ D
  have hL := acceptProb_hyb_last real sim Φ D
  rw [← h0, ← hL]
  have htel := abs_sub_le_sum_hybrids
    (fun k => acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D) L
  have hsum : ∑ k ∈ range L, |acceptProb (fun ω => Φ ω.1 (hybV real sim k ω)) D -
      acceptProb (fun ω => Φ ω.1 (hybV real sim (k + 1) ω)) D| ≤ ∑ _k ∈ range L, g :=
    sum_le_sum fun k hk => by
      obtain ⟨a, ha⟩ := exists_hyb_step real sim Φ D ⟨k, mem_range.1 hk⟩
      exact ha.trans (hg _ a)
  refine htel.trans (hsum.trans (le_of_eq ?_))
  rw [sum_const, card_range, nsmul_eq_mul]

end Chain

/-- **The template's word list**: for `i < L` and `j < L`, entry `j` of
`[f 0, …, f (i−1), v, f (i+1), …, f (L−1)]` is `v` for `j = i` and `f j` otherwise. -/
theorem getD_plug (f : ℕ → List Bool) (v : List Bool) {i L j : ℕ} (hi : i < L) (hj : j < L) :
    ((List.range i).map f ++ v :: (List.range (L - (i + 1))).map fun k => f (i + 1 + k)).getD j
        [] = if j = i then v else f j := by
  rw [List.getD_eq_getElem?_getD]
  rcases lt_trichotomy j i with h | h | h
  · rw [List.getElem?_append_left (by rw [List.length_map, List.length_range]; exact h),
      List.getElem?_map, List.getElem?_range h, Option.map_some, Option.getD_some,
      if_neg (Nat.ne_of_lt h)]
  · subst h
    rw [List.getElem?_append_right (by rw [List.length_map, List.length_range]),
      List.length_map, List.length_range, Nat.sub_self, List.getElem?_cons_zero,
      Option.getD_some, if_pos rfl]
  · obtain ⟨k, rfl⟩ : ∃ k, j = i + 1 + k := ⟨j - (i + 1), by omega⟩
    rw [List.getElem?_append_right (by rw [List.length_map, List.length_range]; omega),
      List.length_map, List.length_range, show i + 1 + k - i = k + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_map, List.getElem?_range (by omega),
      Option.map_some, Option.getD_some, if_neg (by omega)]

end TCSlib.Cryptography.SecureComputation.ComposeProb
