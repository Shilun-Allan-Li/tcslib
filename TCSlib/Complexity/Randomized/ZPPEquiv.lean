/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ExpectedTime
import TCSlib.Complexity.Randomized.PTMEquiv
import TCSlib.Complexity.Randomized.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Expected-time PTM classes as certificate classes

The class-level consequences of [AB09, §7.4.2] and [AB09, Exercise 7.6(a)]: a PTM with
expected polynomial running time, cut at a polynomial number of steps, is a polynomial-time
verifier reading its coins as the random string (`Complexity.exists_choiceVerifier_mem_P`).
Hence `ZPP` (Def 7.7) and its abort form lie in the certificate class
`Randomized.InZPP polyTimeModel`, and so in `RP ∩ coRP` [AB09, Thm 7.8]; and expected-time
bounded error gives exactly `BPP`.

## Main definitions

* `Turing.FinNDTM.BPDecidesInExpTime`, `Randomized.BPP_ExpPTM` — bounded error in expected
  polynomial time [AB09, §7.4.2].

## Main results

* `Randomized.exists_eff_haltRun` — a PTM's halted output on polynomially many coins is a
  polynomial-time zero-error verifier.
* `Randomized.inZPP_of_mem_ZPP_PTM`, `Randomized.inZPP_of_mem_ZPPAbort_PTM`,
  `Randomized.ZPP_PTM_subset_RP_PTM_inter_coRP_PTM`,
  `Randomized.ZPPAbort_PTM_subset_RP_PTM_inter_coRP_PTM` — [AB09, Def 7.7, Ex 7.6, Thm 7.8].
* `Randomized.BPP_ExpPTM_eq_BPP_PTM` — [AB09, §7.4.2]: expected time gives the same `BPP`.

## Divergences

* "`Pr[M(x) = L(x)] ≥ 2/3`" for a machine that need not halt is read as the supremum over
  `t` of `Pr[halted within t steps with output L(x)]`, i.e. `∀ ε > 0, ∃ t, 2/3 - ε ≤ …`.
* The converse inclusions (`InZPP polyTimeModel ⊆ ZPP_PTM`, `RP ∩ coRP ⊆ ZPP_PTM`) need the
  restart host; they are `Randomized.inZPP_subset_ZPP_PTM` and
  `Randomized.ZPP_PTM_eq_RP_PTM_inter_coRP_PTM` in
  `TCSlib.Complexity.Randomized.ZPPHostsClasses`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing.FinNDTM

/-- `N` decides `L` with bounded error in expected time `T`: `E[T_{N,x}] ≤ T(|x|)`, and the
probability of halting with output `[L(x)]` (as a supremum over time) is at least `2/3`.
[AB09, §7.4.2] -/
def BPDecidesInExpTime (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool, N.ExpTimeLe x (T x.length) ∧ ∀ ε : ℚ, 0 < ε → ∃ t : ℕ,
    2 / 3 - ε ≤ Randomized.randProb t
      (fun w => N.haltRun x w = some [MultiTapeTM.indicator (L : Set (List Bool)) x])

end Turing.FinNDTM

namespace Randomized

open Complexity Turing

/-- `BPP` with expected running time: `⋃_e {L | some PTM decides L with bounded error in
expected time c·(n^e + 1)}`. [AB09, §7.4.2] -/
def BPP_ExpPTM : Set (Language Bool) :=
  ⋃ e : ℕ, {L | ∃ (c : ℕ) (N : FinNDTM Bool), N.BPDecidesInExpTime L fun n => c * (n ^ e + 1)}

/-- The halted output of a PTM `N` on `polyLen A e |x|` coins is a polynomial-time zero-error
verifier: `M(x, r) = some b` iff `N` has halted on `x` under `r` with output `[b]`.

**Proof sketch.** `exists_choiceVerifier_mem_P` gives `P`-languages `V₁` for `N` and `V₀` for
`N.flipOutput` recognising "halted with output `[1]`" on `x ++ r`; for the flipped machine this
is "halted with output `[0]`". Let `M` answer `1` on `V₁`, else `0` on `V₀`, else nothing. Its
two answer sets are preimages of `V₁` and `V₀ \ V₁` under the polynomial-time map
`⟨x, r⟩ ↦ x ++ r`, hence in `P`. -/
theorem exists_eff_haltRun (N : FinNDTM Bool) (A e : ℕ) :
    ∃ M : List Bool → List Bool → Option Bool, polyTimeModel.Eff M ∧
      ∀ (x r : List Bool) (b : Bool), r.length = polyLen A e x.length →
        (M x r = some b ↔ N.haltRun x r = some [b]) := by
  classical
  obtain ⟨V₁, hV₁, h₁⟩ := exists_choiceVerifier_mem_P N A e
  obtain ⟨V₀, hV₀, h₀⟩ := exists_choiceVerifier_mem_P N.flipOutput A e
  set g : List Bool → List Bool := fun z => pairFstD z ++ pairSndD z
  have hg : PolyTimeComputable g :=
    polyTimeComputable_pairFstD.append polyTimeComputable_pairSndD
  refine ⟨fun x r => if x ++ r ∈ V₁ then some true else if x ++ r ∈ V₀ then some false else none,
    ⟨g ⁻¹' V₁, {z | z ∈ g ⁻¹' V₀ ∧ z ∈ (g ⁻¹' V₁)ᶜ}, preimage_mem_P hV₁ hg,
      inter_mem_P (preimage_mem_P hV₀ hg) (compl_mem_P (preimage_mem_P hV₁ hg)),
      fun x r => ?_⟩, fun x r b hr => ?_⟩
  · have hgx : g (pairEncode x r) = x ++ r := by
      simp [g, pairFstD_pairEncode, pairSndD_pairEncode]
    show ((if x ++ r ∈ V₁ then some true else if x ++ r ∈ V₀ then some false else none) =
        some true ↔ g (pairEncode x r) ∈ V₁) ∧
      ((if x ++ r ∈ V₁ then some true else if x ++ r ∈ V₀ then some false else none) =
        some false ↔ g (pairEncode x r) ∈ V₀ ∧ g (pairEncode x r) ∉ V₁)
    rw [hgx]
    by_cases h1 : x ++ r ∈ V₁ <;> by_cases h0 : x ++ r ∈ V₀ <;> simp [h1, h0]
  · have h1 : x ++ r ∈ V₁ ↔ N.haltRun x r = some [true] :=
      (h₁ x r hr).trans FinNDTM.haltRun_eq_some_iff.symm
    have h0 : x ++ r ∈ V₀ ↔ N.haltRun x r = some [false] := by
      refine (h₀ x r hr).trans (FinNDTM.haltRun_eq_some_iff.symm.trans ?_)
      rw [FinNDTM.haltRun_flipOutput]
      cases N.haltRun x r with
      | none => simp
      | some o =>
        simp only [Option.map_some, Option.some.injEq]
        exact ⟨fun h => by simpa using congrArg (List.map not) h, fun h => by rw [h]; rfl⟩
    show (if x ++ r ∈ V₁ then some true else if x ++ r ∈ V₀ then some false else none) =
        some b ↔ _
    by_cases hv1 : x ++ r ∈ V₁
    · rw [if_pos hv1, h1.mp hv1]
      cases b <;> simp
    · rw [if_neg hv1]
      by_cases hv0 : x ++ r ∈ V₀
      · rw [if_pos hv0, h0.mp hv0]
        cases b <;> simp
      · rw [if_neg hv0]
        cases b
        · exact ⟨fun h => absurd h (by simp), fun h => absurd (h0.mpr h) hv0⟩
        · exact ⟨fun h => absurd h (by simp), fun h => absurd (h1.mpr h) hv1⟩

/-- **Expected-time `ZPP` in certificate form** [AB09, Def 7.7 and Exercise 7.6(a)]: a
zero-error PTM with expected time `c(n^e + 1)` gives an `InZPP polyTimeModel` verifier.

**Proof sketch.** Cut the run at `Q = 4c(|x|+1)^e ≥ 2c(|x|^e + 1)` steps (`choiceBudget_le`)
and use `exists_eff_haltRun`. By `ZDecidesInTime.truncate` every halted answer is `L(x)`,
and the run has halted with probability at least `1 - c(|x|^e+1)/Q ≥ 1/2`. -/
theorem inZPP_of_mem_ZPP_PTM {L : Language Bool} (h : L ∈ ZPP_PTM) :
    InZPP polyTimeModel L := by
  classical
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  obtain ⟨M, hEff, hM⟩ := exists_eff_haltRun N (4 * c) e
  refine ⟨M, 4 * c, e, hEff, fun x => ?_⟩
  set B := c * (x.length ^ e + 1)
  set Q := polyLen (4 * c) e x.length
  have hQ : 2 * B ≤ Q := by
    have := choiceBudget_le (2 * c) e x.length
    simp only [Q, B, polyLen] at this ⊢
    nlinarith [this]
  have hB1 : (1 : ℚ) ≤ B := (hN x).1.one_le
  have hQpos : 0 < Q := by
    have : 1 ≤ B := by exact_mod_cast hB1
    omega
  obtain ⟨hcorr, hprob⟩ := hN.truncate x hQpos
  have hprob' : 1 - (B : ℚ) / Q ≤ randProb Q (fun w =>
      N.haltRun x w = some [MultiTapeTM.indicator (L : Set (List Bool)) x]) := hprob
  have hhalf : (B : ℚ) / Q ≤ 1 / 2 := by
    have hQ' : (2 * B : ℚ) ≤ Q := by exact_mod_cast hQ
    rw [div_le_iff₀ (by exact_mod_cast hQpos)]
    linarith
  have hspec : ∀ (r : Fin Q → Bool) (b : Bool), M x (List.ofFn r) = some b →
      b = MultiTapeTM.indicator (L : Set (List Bool)) x := fun r b hb => by
    have := hcorr _ _ ((hM x _ b List.length_ofFn).mp hb)
    simpa using this
  refine ⟨fun hx r hr => ?_, fun hx r hr => ?_, ?_⟩
  · have := hspec r false hr
    simp [MultiTapeTM.indicator, hx] at this
  · have := hspec r true hr
    simp [MultiTapeTM.indicator, hx] at this
  · calc randProb Q (fun r => M x r = none)
        ≤ randProb Q (fun r => ¬ N.haltRun x r =
            some [MultiTapeTM.indicator (L : Set (List Bool)) x]) :=
          randProb_mono fun r hr heq => by
            rw [← hM x _ _ List.length_ofFn, hr] at heq
            exact absurd heq (by simp)
      _ = 1 - randProb Q (fun r => N.haltRun x r =
            some [MultiTapeTM.indicator (L : Set (List Bool)) x]) := randProb_not _
      _ ≤ 1 / 2 := by linarith

/-- **Abort form ⊆ `InZPP`** [AB09, Exercise 7.6(a)]: a polynomial-time PTM with outputs in
`{0, 1, ?}`, never wrong and with `Pr[?] ≤ 1/2`, gives an `InZPP polyTimeModel` verifier.

**Proof sketch.** With `T = a(|x|^e + 1) ≤ Q = 2a(|x|+1)^e`, every branch has halted after
`Q` coins with the output of its first `T` coins. `exists_eff_haltRun` reads that output as
`some b` exactly when it is `[b]`; it is never `[¬L(x)]`, and `?` occurs only when the output
is not `[L(x)]`, which has probability at most `1/2` (`randProb_take`). -/
theorem inZPP_of_mem_ZPPAbort_PTM {L : Language Bool} (h : L ∈ ZPPAbort_PTM) :
    InZPP polyTimeModel L := by
  classical
  obtain ⟨e, a, N, hN⟩ := Set.mem_iUnion.mp h
  obtain ⟨M, hEff, hM⟩ := exists_eff_haltRun N (2 * a) e
  refine ⟨M, 2 * a, e, hEff, fun x => ?_⟩
  have hNx := hN x
  dsimp only at hNx
  obtain ⟨hhalt, hwrong, hprob⟩ := hNx
  set T := a * (x.length ^ e + 1)
  set Q := polyLen (2 * a) e x.length
  set ℓ := MultiTapeTM.indicator (L : Set (List Bool)) x
  have hTQ : T ≤ Q := choiceBudget_le a e x.length
  have hrun : ∀ r : List Bool, r.length = Q →
      N.haltRun x r = some (N.outputWith x (r.take T)) := fun r hr => by
    have hle : T ≤ r.length := hr ▸ hTQ
    rw [FinNDTM.haltRun_eq_some_iff]
    refine ⟨hhalt.mono hle r rfl, ?_⟩
    unfold FinNDTM.outputWith
    rw [FinNDTM.runWith_eq_runWith_take hhalt hle]
  have hspec : ∀ (r : Fin Q → Bool) (b : Bool), M x (List.ofFn r) = some b → b = ℓ :=
    fun r b hb => by
      rw [hM x _ b List.length_ofFn, hrun _ List.length_ofFn, Option.some.injEq] at hb
      have := hwrong (List.take T (List.ofFn r))
        (List.length_take_of_le (by rw [List.length_ofFn]; exact hTQ))
      rw [hb] at this
      cases b <;> cases hl : ℓ <;> simp_all
  refine ⟨fun hx r hr => ?_, fun hx r hr => ?_, ?_⟩
  · have := hspec r false hr
    simp [ℓ, MultiTapeTM.indicator, hx] at this
  · have := hspec r true hr
    simp [ℓ, MultiTapeTM.indicator, hx] at this
  · unfold FinNDTM.outputProb at hprob
    calc randProb Q (fun r => M x r = none)
        ≤ randProb Q (fun r => ¬ N.outputWith x (r.take T) = [ℓ]) :=
          randProb_mono fun r hr heq => by
            rw [← Option.some.injEq, ← hrun _ List.length_ofFn,
              ← hM x _ _ List.length_ofFn, hr] at heq
            exact absurd heq (by simp)
      _ = 1 - randProb Q (fun r => N.outputWith x (r.take T) = [ℓ]) := randProb_not _
      _ = 1 - randProb T (fun w => N.outputWith x w = [ℓ]) := by
          rw [randProb_take hTQ (fun w => N.outputWith x w = [ℓ])]
      _ ≤ 1 / 2 := by linarith

/-- **`ZPP ⊆ RP ∩ coRP`** [AB09, Thm 7.8], PTM form. -/
theorem ZPP_PTM_subset_RP_PTM_inter_coRP_PTM : ZPP_PTM ⊆ RP_PTM ∩ coRP_PTM := fun L h =>
  have hz := (zpp_eq_rp_inter_corp_polyTime L).mp (inZPP_of_mem_ZPP_PTM h)
  ⟨(mem_RP_PTM_iff L).mpr hz.1, (mem_coRP_PTM_iff L).mpr hz.2⟩

/-- The abort-form class lies in `RP ∩ coRP`. [AB09, Exercise 7.6] -/
theorem ZPPAbort_PTM_subset_RP_PTM_inter_coRP_PTM : ZPPAbort_PTM ⊆ RP_PTM ∩ coRP_PTM :=
  fun L h =>
  have hz := (zpp_eq_rp_inter_corp_polyTime L).mp (inZPP_of_mem_ZPPAbort_PTM h)
  ⟨(mem_RP_PTM_iff L).mpr hz.1, (mem_coRP_PTM_iff L).mpr hz.2⟩

/-- **Expected time ⇒ `BPP`** [AB09, §7.4.2]: a bounded-error PTM with expected time
`c(n^e + 1)` gives an `InBPP polyTimeModel` verifier.

**Proof sketch.** With `B = c(|x|^e + 1)` and `Q = 200c(|x|+1)^e ≥ 100 B`, Markov truncation
(`haltProb_le_truncate`, `haltProb_mono`) gives `Pr_Q[halted with L(x)] ≥ 2/3 - 1/100 ≥ 5/8`.
The choice-word verifier for `[1]` at length `Q` accepts exactly on those coins for `x ∈ L`
and rejects at least on them for `x ∉ L`; `InBPPAt.inBPP_of_5_8` amplifies to `2/3`. -/
theorem inBPP_of_mem_BPP_ExpPTM {L : Language Bool} (h : L ∈ BPP_ExpPTM) :
    InBPP polyTimeModel L := by
  classical
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  obtain ⟨V, hVP, hV⟩ := exists_choiceVerifier_mem_P N (200 * c) e
  refine InBPPAt.inBPP_of_5_8 polyTimeModel_closedUnderMajority
    ⟨fun x r => MultiTapeTM.indicator V (x ++ r), 200 * c, e, eff_append_mem hVP, fun x => ?_⟩
  have hNx := hN x
  dsimp only at hNx
  obtain ⟨hexp, hlim⟩ := hNx
  set B := c * (x.length ^ e + 1)
  set Q := polyLen (200 * c) e x.length
  set ℓ := MultiTapeTM.indicator (L : Set (List Bool)) x
  have hBQ : 100 * B ≤ Q := by
    have := choiceBudget_le (100 * c) e x.length
    simp only [Q, B, polyLen] at this ⊢
    nlinarith [this]
  have hge : 5 / 8 ≤ randProb Q (fun w => N.haltRun x w = some [ℓ]) := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨t, ht⟩ := hlim (2 / 3 - 1 / 100 - 5 / 8) (by norm_num)
    have h1 := FinNDTM.haltProb_le_truncate hexp [ℓ] t
    have h2 := FinNDTM.haltProb_mono (N := N) (x := x) [ℓ] hBQ
    linarith
  have hacc : ∀ r : Fin Q → Bool, MultiTapeTM.indicator V (x ++ List.ofFn r) = true ↔
      N.haltRun x (List.ofFn r) = some [true] := fun r => by
    rw [indicator_eq_true_iff]
    exact (hV x _ List.length_ofFn).trans FinNDTM.haltRun_eq_some_iff.symm
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · refine le_trans hge (randProb_mono fun r hr => (hacc r).mpr ?_)
    simpa [ℓ, MultiTapeTM.indicator, hx] using hr
  · refine le_trans hge (randProb_mono fun r hr => ?_)
    have hf : N.haltRun x (List.ofFn r) = some [false] := by
      simpa [ℓ, MultiTapeTM.indicator, hx] using hr
    show MultiTapeTM.indicator V (x ++ List.ofFn r) = false
    cases hi : MultiTapeTM.indicator V (x ++ List.ofFn r)
    · rfl
    · rw [(hacc r).mp hi] at hf; exact absurd hf (by simp)

/-- A worst-case bounded-error PTM is an expected-time one. [AB09, §7.4.2] -/
theorem BPP_PTM_subset_BPP_ExpPTM : BPP_PTM ⊆ BPP_ExpPTM := by
  intro L h
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  refine Set.mem_iUnion.mpr ⟨e, c, N, fun x => ?_⟩
  have hNx := hN x
  dsimp only at hNx
  obtain ⟨hhalt, hprob⟩ := hNx
  refine ⟨FinNDTM.expTimeLe_of_haltsWithin hhalt, fun ε hε => ⟨c * (x.length ^ e + 1), ?_⟩⟩
  have heq : randProb (c * (x.length ^ e + 1)) (fun w => N.haltRun x w =
      some [MultiTapeTM.indicator (L : Set (List Bool)) x]) =
      N.outputProb x (c * (x.length ^ e + 1)) [MultiTapeTM.indicator (L : Set (List Bool)) x] :=
    randProb_congr fun r => by
      rw [FinNDTM.haltRun_eq_some_iff]
      exact ⟨fun h => h.2, fun h => ⟨hhalt _ List.length_ofFn, h⟩⟩
  rw [heq]
  linarith

/-- **Expected time gives the same `BPP`** [AB09, §7.4.2]. -/
theorem BPP_ExpPTM_eq_BPP_PTM : BPP_ExpPTM = BPP_PTM :=
  Set.Subset.antisymm (fun _ h => (mem_BPP_PTM_iff _).mpr (inBPP_of_mem_BPP_ExpPTM h))
    BPP_PTM_subset_BPP_ExpPTM

end Randomized
