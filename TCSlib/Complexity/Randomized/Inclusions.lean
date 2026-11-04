/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.PTM
import TCSlib.Complexity.Randomized.PolyTimeModel
import TCSlib.Complexity.ClassNP.Nondeterminism
import TCSlib.Complexity.CookLevin.Hardness
import TCSlib.Complexity.CircuitComplexity.KarpLipton
import TCSlib.Complexity.CircuitComplexity.MeyerSigmaEXP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Easy inclusions between randomized and classical classes

The remarks of [AB09, Ch. 7] relating `BPP`, `RP`, `coRP` to `P`, `NP`, `EXP` and `PH`, in the
PTM form (`Randomized.BPP_PTM` etc.) and in the certificate form
(`Randomized.InBPP polyTimeModel` etc.), and the error reduction for `RP` of [AB09, Ex 7.4].

## Main definitions

* `Randomized.InRPWeak`, `Randomized.InRPStrong` — `RP` with acceptance probability
  `(|x|+1)^{-c}`, resp. `1 − 2^{-((|x|+1)^d + 1)}` [AB09, Ex 7.4].

## Main results

* `Randomized.P_subset_BPP_PTM`, `Randomized.inBPP_polyTimeModel_of_mem_P` — `P ⊆ BPP`
  [AB09, p. 126].
* `Randomized.RP_PTM_subset_NP`, `Randomized.mem_NP_of_inRP_polyTimeModel` — `RP ⊆ NP`
  [AB09, p. 131].
* `Randomized.RP_PTM_subset_BPP_PTM`, `Randomized.coRP_PTM_subset_BPP_PTM`, `Randomized.InRP.inBPP`,
  `Randomized.InCoRP.inBPP`, `Randomized.InCoRP.inBPP_polyTime` — `RP, coRP ⊆ BPP`
  [AB09, p. 132].
* `Randomized.mem_EXP_of_inBPP_polyTimeModel` — `BPP ⊆ EXP` [AB09, p. 126].
* `Randomized.inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP` — `NP = P ⇒ BPP = P` [AB09, p. 135].
* `Randomized.InBPP.of_polyTimeReducible`, `Randomized.InRP.of_polyTimeReducible`,
  `Randomized.InCoRP.of_polyTimeReducible` — `BPP`, `RP`, `coRP` are closed under `≤ₚ`
  (through `Randomized.exists_eff_reducedVerifier`).
* `Randomized.PH_eq_SigmaP_two_of_inBPP_SAT3` — `3SAT ∈ BPP ⇒ PH = Σ₂ᵖ` [AB09, p. 135].
* `Randomized.rp_error_reduction` — [AB09, Ex 7.4].

## Divergences

* `BPP ⊆ EXP`, `NP = P ⇒ BPP = P`, the `3SAT` corollary and [AB09, Ex 7.4] (printed for a
  "polynomial-time PTM") are stated for the certificate form; the PTM forms follow from the
  equivalence of [AB09, Defs 7.2 and 7.3] (unit U2).  Moreover `BPP ⊆ EXP` is proved
  through `BPP ⊆ Σ₂ᵖ ⊆ EXP` (`sipser_gacs_polyTime`, `Complexity.SigmaP_two_subset_EXP`)
  rather than by enumerating coins.
* [AB09, Ex 7.4] assumes `Pr[accept] ≥ n^{-c}`, which is meaningless at `n = 0`; we assume
  `min (2/3) ((n+1)^{-c})`, implied by the book's bound for `n ≥ 1`, and conclude
  `1 − 2^{-((n+1)^d+1)} ≥ 1 − 2^{-n^d}` (the `InBPPStrong` convention).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Turing.FinNDTM

/-- A one-sided-error PTM decider is a nondeterministic decider: every accepting branch is a
certificate. [AB09, p. 131] -/
theorem RDecidesInTime.decidesInTime {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ}
    (h : N.RDecidesInTime L T) : N.DecidesInTime L T := by
  intro x
  obtain ⟨hhalt, hin, hout⟩ := h x
  refine ⟨hhalt, ⟨fun hx => ?_, fun ⟨w, hw, _, hacc⟩ => ?_⟩⟩
  · obtain ⟨w, hw, hwout⟩ :=
      exists_outputWith_of_outputProb_pos (lt_of_lt_of_le (by norm_num) (hin hx))
    exact ⟨w, hw, hhalt w hw, hwout⟩
  · by_contra hx
    have hf : N.outputWith x w = [false] := hout hx w hw
    exact absurd (hf.symm.trans hacc) (by decide)

end Turing.FinNDTM

namespace Randomized

open Complexity Turing

/-! ### PTM form -/

/-- `DTIME(T) ⊆ BPTIME(T)`: a deterministic machine is a PTM whose two transition functions
coincide. [AB09, p. 126] -/
theorem DTIME_subset_BPTIME (T : ℕ → ℕ) : DTIME T ⊆ BPTIME T := by
  classical
  rintro L ⟨c, M, hM⟩
  refine ⟨c, M.toFinNDTM, fun x => ?_⟩
  obtain ⟨hhalt, hout⟩ := (M.computesInTime_iff _ _ _).mp (hM x)
  have hrun : ∀ w : List Bool, M.toFinNDTM.tm.runWith w (M.toFinNDTM.tm.initCfg x) =
      M.tm.runFrom (M.tm.initCfg x) w.length := fun w =>
    M.tm.toNDTM_runWith w (M.tm.initCfg x)
  refine ⟨fun w hw => by rw [hrun, hw]; exact hhalt, ?_⟩
  rw [FinNDTM.outputProb_eq_one fun w hw => by
    rw [FinNDTM.outputWith, hrun, hw]; exact hout]
  norm_num

/-- **`P ⊆ BPP`** (PTM form). [AB09, p. 126] -/
theorem P_subset_BPP_PTM : P ⊆ BPP_PTM :=
  Set.iUnion_mono fun _ => DTIME_subset_BPTIME _

/-- `RTIME(T) ⊆ NTIME(T)`. [AB09, p. 131] -/
theorem RTIME_subset_NTIME (T : ℕ → ℕ) : RTIME T ⊆ NTIME T := by
  rintro L ⟨c, N, hN⟩
  exact ⟨c, N, hN.decidesInTime⟩

/-- **`RP ⊆ NP`** (PTM form): every accepting branch is a certificate. [AB09, p. 131] -/
theorem RP_PTM_subset_NP : RP_PTM ⊆ NP := by
  rw [NP_eq_iUnion_NTIME]
  exact Set.iUnion_mono fun _ => RTIME_subset_NTIME _

/-- **`RP ⊆ BPP`** (PTM form). [AB09, p. 132] -/
theorem RP_PTM_subset_BPP_PTM : RP_PTM ⊆ BPP_PTM :=
  Set.iUnion_mono fun _ => RTIME_subset_BPTIME _

/-- **`coRP ⊆ BPP`** (PTM form). [AB09, p. 132] -/
theorem coRP_PTM_subset_BPP_PTM : coRP_PTM ⊆ BPP_PTM := by
  intro L hL
  have h := compl_mem_BPP_PTM (RP_PTM_subset_BPP_PTM hL)
  rwa [compl_compl] at h

/-! ### Certificate form -/

/-- **`RP ⊆ BPP`** (certificate form): an `RP` verifier never errs on non-members. [AB09, p. 132] -/
theorem InRP.inBPP {E : VerifierModel} {L : Language Bool} (h : InRP E L) : InBPP E L := by
  obtain ⟨M, a, k, hM, hL⟩ := h
  refine ⟨M, a, k, hM, fun x => ⟨(hL x).1, fun hx => ?_⟩⟩
  rw [randProb_congr (B := fun _ => True) fun r => by simp [(hL x).2 hx r], randProb_true]
  norm_num

/-- **`coRP ⊆ BPP`** (certificate form), for a model closed under negation. [AB09, p. 132] -/
theorem InCoRP.inBPP {E : VerifierModel} (hNot : ClosedUnderNot E) {L : Language Bool}
    (h : InCoRP E L) : InBPP E L := by
  have h' := InBPP.compl E hNot (InRP.inBPP h)
  rwa [compl_compl] at h'

/-- **`coRP ⊆ BPP`** for polynomial-time verifiers (certificate form). [AB09, p. 132] -/
theorem InCoRP.inBPP_polyTime {L : Language Bool} (h : InCoRP polyTimeModel L) :
    InBPP polyTimeModel L :=
  InCoRP.inBPP polyTimeModel_closedUnderNot h

/-- **`P ⊆ BPP`** (certificate form): the verifier `M(x, r) = L(x)` ignores its coins.
[AB09, p. 126] -/
theorem inBPP_polyTimeModel_of_mem_P {L : Language Bool} (hL : L ∈ P) :
    InBPP polyTimeModel L := by
  classical
  refine ⟨fun x _ => decide (x ∈ L), 0, 0,
    ⟨pairFstD ⁻¹' L, pairFstD ⁻¹' Lᶜ, preimage_mem_P hL polyTimeComputable_pairFstD,
      preimage_mem_P (compl_mem_P hL) polyTimeComputable_pairFstD, fun x r => ?_⟩,
    fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · show (_ ↔ pairFstD (Turing.pairEncode x r) ∈ L) ∧
      (_ ↔ pairFstD (Turing.pairEncode x r) ∈ Lᶜ)
    simp only [boolVerifier, pairFstD_pairEncode, Option.some.injEq, decide_eq_true_eq,
      decide_eq_false_iff_not]
    constructor
    all_goals trivial
  · rw [randProb_congr (B := fun _ => True) fun r => by simp [hx], randProb_true]
    norm_num
  · rw [randProb_congr (B := fun _ => True) fun r => by simp [hx], randProb_true]
    norm_num

/-- **`RP ⊆ NP`** (certificate form): an accepted random string is a certificate.
[AB09, p. 131]

**Proof sketch.** The `NP` verifier accepts `⟨x, u⟩` iff the `RP` verifier accepts `(x, u)` and
`|u| = polyLen a k |x|`; it is in `P` by `inter_mem_P` and `lenEq_preimage_mem_P`.  Members
have an accepted random string since acceptance has probability `≥ 2/3 > 0`
(`exists_ofFn_of_randProb_pos`); conversely an accepted `u` of the right length is a random
string (`exists_ofFn_eq`), so soundness of the `RP` verifier forces `x ∈ L`. -/
theorem mem_NP_of_inRP_polyTimeModel {L : Language Bool} (h : InRP polyTimeModel L) :
    L ∈ NP := by
  classical
  obtain ⟨M, a, k, ⟨V₁, V₀, hV₁, -, hM⟩, hL⟩ := h
  have hlen : {z : List Bool | (pairSndD z).length =
      (((fun y : List Bool => List.replicate (a * (y.length + 1) ^ k) true) ∘ pairFstD) z).length}
      ∈ P :=
    lenEq_preimage_mem_P polyTimeComputable_pairSndD
      ((polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD)
  refine mem_NP_iff_exists_length_le.mpr ⟨a, k, _, inter_mem_P hV₁ hlen, fun x => ?_⟩
  have hMt : ∀ u, M x u = true ↔ Turing.pairEncode x u ∈ V₁ := fun u => by
    simpa only [boolVerifier, Option.some.injEq] using (hM x u).1
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := exists_ofFn_of_randProb_pos
      (lt_of_lt_of_le (by norm_num) ((hL x).1 hx))
    refine ⟨List.ofFn r, by simp [polyLen], (hMt _).mp hr, ?_⟩
    show (pairSndD (Turing.pairEncode x (List.ofFn r))).length =
      (List.replicate _ true).length
    simp [polyLen]
  · rintro ⟨u, -, hu, hlenu⟩
    have hlenu' : u.length = polyLen a k x.length := by
      change (pairSndD (Turing.pairEncode x u)).length =
        (List.replicate (a * ((pairFstD (Turing.pairEncode x u)).length + 1) ^ k) true).length
        at hlenu
      simpa [polyLen] using hlenu
    by_contra hx
    obtain ⟨r, rfl⟩ := exists_ofFn_eq hlenu'
    have := (hL x).2 hx r
    rw [(hMt _).mpr hu] at this
    exact absurd this (by decide)

/-- **`BPP ⊆ EXP`** (certificate form). [AB09, p. 126] -/
theorem mem_EXP_of_inBPP_polyTimeModel {L : Language Bool} (h : InBPP polyTimeModel L) :
    L ∈ EXP :=
  SigmaP_two_subset_EXP (sipser_gacs_polyTime h).1

/-- **`NP = P ⇒ BPP = P`** (certificate form), via `BPP ⊆ Σ₂ᵖ` and the collapse `PH = P`.
[AB09, p. 135 and p. 140] -/
theorem inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP (h : P = NP) (L : Language Bool) :
    InBPP polyTimeModel L ↔ L ∈ P := by
  refine ⟨fun hL => ?_, inBPP_polyTimeModel_of_mem_P⟩
  rw [← PH_eq_P_of_P_eq_NP h]
  exact SigmaP_subset_PH 2 (sipser_gacs_polyTime hL).1

/-- **The reduced verifier**: for a polynomial-time `f` and an efficient verifier `M` drawing
`polyLen a k` coins, running `M` on `f x` with the matching prefix of the coins is an efficient
verifier, and some polynomial schedule in `|x|` dominates the schedule in `|f x|`.

**Proof sketch.** The new verifier's answer sets are preimages of the old ones under the
polynomial-time map `⟨x, r⟩ ↦ ⟨f x, r'⟩` (`sliceTake`); `|f x|` is polynomial in `|x|`
(`PolyTimeComputable.output_length_le`), which bounds the schedule. -/
theorem exists_eff_reducedVerifier {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    {M : List Bool → List Bool → Bool} {a k : ℕ} (hM : polyTimeModel.Eff (boolVerifier M)) :
    ∃ a' k', polyTimeModel.Eff
        (boolVerifier fun x r => M (f x) (r.take (polyLen a k (f x).length))) ∧
      ∀ x : List Bool, polyLen a k (f x).length ≤ polyLen a' k' x.length := by
  classical
  obtain ⟨C, c, hC⟩ := hf.output_length_le
  obtain ⟨V₁, V₀, hV₁, hV₀, hM⟩ := hM
  let g : List Bool → List Bool := fun z =>
    sliceTake a k (Turing.pairEncode (f (pairFstD z)) (pairSndD z))
  have hg : PolyTimeComputable g := (polyTimeComputable_sliceTake a k).comp
    ((hf.comp polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)
  have hgx : ∀ x r, g (Turing.pairEncode x r) =
      Turing.pairEncode (f x) (r.take (polyLen a k (f x).length)) := by
    intro x r
    simp [g, sliceTake]
  refine ⟨a * (C + 1) ^ k, c * k,
    ⟨g ⁻¹' V₁, g ⁻¹' V₀, preimage_mem_P hV₁ hg, preimage_mem_P hV₀ hg, fun x r => ?_⟩,
    fun x => ?_⟩
  · show (_ ↔ g (Turing.pairEncode x r) ∈ V₁) ∧ (_ ↔ g (Turing.pairEncode x r) ∈ V₀)
    rw [hgx]
    exact hM (f x) _
  · have hp : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
    have h1 : (f x).length + 1 ≤ (C + 1) * (x.length + 1) ^ c := by
      calc (f x).length + 1 ≤ C * (x.length + 1) ^ c + (x.length + 1) ^ c :=
            Nat.add_le_add (hC x) hp
        _ = (C + 1) * (x.length + 1) ^ c := by ring
    calc polyLen a k (f x).length = a * ((f x).length + 1) ^ k := rfl
      _ ≤ a * ((C + 1) * (x.length + 1) ^ c) ^ k :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 k)
      _ = polyLen (a * (C + 1) ^ k) (c * k) x.length := by
          unfold polyLen
          rw [mul_pow, ← pow_mul]
          ring

/-- **`BPP` is closed under polynomial-time Karp reductions** (certificate form): if
`L' ≤ₚ L` and `L ∈ BPP` then `L' ∈ BPP`.

**Proof sketch.** Run the verifier of `L` on `f x` with the prefix of the random string it
draws on inputs of length `|f x|` (`exists_eff_reducedVerifier`); padding coins are ignored
(`randProb_take`). -/
theorem InBPP.of_polyTimeReducible {L L' : Language Bool} (hred : L' ≤ₚ L)
    (h : InBPP polyTimeModel L) : InBPP polyTimeModel L' := by
  classical
  obtain ⟨f, hf, hfL⟩ := hred
  obtain ⟨M, a, k, hM, hL⟩ := h
  obtain ⟨a', k', hE, hle⟩ := exists_eff_reducedVerifier (a := a) (k := k) hf hM
  refine ⟨_, a', k', hE, fun x => ?_⟩
  have key : ∀ b : Bool, randProb (polyLen a' k' x.length)
      (fun r => M (f x) (r.take (polyLen a k (f x).length)) = b) =
      randProb (polyLen a k (f x).length) (fun s => M (f x) s = b) := fun b =>
    randProb_take (hle x) (fun s => M (f x) s = b)
  rw [key, key]
  exact ⟨fun hx => (hL (f x)).1 ((hfL x).mp hx),
    fun hx => (hL (f x)).2 fun hfx => hx ((hfL x).mpr hfx)⟩

/-- **`RP` is closed under polynomial-time Karp reductions** (certificate form).

**Proof sketch.** As `InBPP.of_polyTimeReducible`; every prefix of a random string is a random
string of its length (`exists_ofFn_eq`), so non-members are never accepted. -/
theorem InRP.of_polyTimeReducible {L L' : Language Bool} (hred : L' ≤ₚ L)
    (h : InRP polyTimeModel L) : InRP polyTimeModel L' := by
  classical
  obtain ⟨f, hf, hfL⟩ := hred
  obtain ⟨M, a, k, hM, hL⟩ := h
  obtain ⟨a', k', hE, hle⟩ := exists_eff_reducedVerifier (a := a) (k := k) hf hM
  refine ⟨_, a', k', hE, fun x => ⟨fun hx => ?_, fun hx r => ?_⟩⟩
  · rw [randProb_take (hle x) (fun s => M (f x) s = true)]
    exact (hL (f x)).1 ((hfL x).mp hx)
  · obtain ⟨r', hr'⟩ := exists_ofFn_eq (m := polyLen a k (f x).length)
      (l := (List.ofFn r).take (polyLen a k (f x).length)) (by simp [hle x])
    show M (f x) _ = false
    rw [hr']
    exact (hL (f x)).2 (fun hfx => hx ((hfL x).mpr hfx)) r'

/-- **`coRP` is closed under polynomial-time Karp reductions** (certificate form). -/
theorem InCoRP.of_polyTimeReducible {L L' : Language Bool} (hred : L' ≤ₚ L)
    (h : InCoRP polyTimeModel L) : InCoRP polyTimeModel L' := by
  obtain ⟨f, hf, hfL⟩ := hred
  exact InRP.of_polyTimeReducible (L := Lᶜ) (L' := L'ᶜ)
    ⟨f, hf, fun x => show x ∉ L' ↔ f x ∉ L from not_congr (hfL x)⟩ h

/-- **`3SAT ∈ BPP ⇒ PH = Σ₂ᵖ`**: `NP` would reduce to `BPP ⊆ P/poly` (Adleman), and Karp–Lipton
collapses the hierarchy. [AB09, p. 135, §7.5.1] -/
theorem PH_eq_SigmaP_two_of_inBPP_SAT3 (h : InBPP polyTimeModel SAT3) : PH = SigmaP 2 :=
  PH_eq_SigmaP_two_of_NP_subset_PPoly fun L hL =>
    (BoolCircuit.mem_PPoly_iff L).mpr
      (adleman_polyTime (InBPP.of_polyTimeReducible (SAT3_NPHard L hL) h))

/-! ### Error reduction for `RP` -/

variable (E : VerifierModel)

/-- `L ∈ RP` with acceptance probability only `min (2/3) ((|x|+1)^{-c})` on members (and never
accepting non-members). [AB09, Ex 7.4] -/
def InRPWeak (c : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → min (2/3) (((x.length + 1 : ℚ) ^ c)⁻¹) ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool, M x (List.ofFn r) = false)

/-- `L ∈ RP` with acceptance probability at least `1 − 2^{-((|x|+1)^d + 1)}` on members.
[AB09, Ex 7.4] -/
def InRPStrong (d : ℕ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    E.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → 1 - (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤
        randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool, M x (List.ofFn r) = false)

/-- The amplified form implies plain `RP` membership with the same verifier. -/
theorem InRPStrong.toInRP {d : ℕ} {L : Language Bool} (hL : InRPStrong E d L) : InRP E L := by
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨M, a, k, hM, fun x => ⟨fun hx => ?_, (hprop x).2⟩⟩
  have he : 2 ≤ (x.length + 1) ^ d + 1 := by
    have := Nat.one_le_pow d (x.length + 1) (by omega)
    omega
  have h2 : (1/2 : ℚ) ^ ((x.length + 1) ^ d + 1) ≤ (1/2 : ℚ) ^ 2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) he
  norm_num at h2
  linarith [(hprop x).1 hx]

/-- Plain `RP` membership implies the weak form, since the weak threshold is at most `2/3`. -/
theorem InRP.toInRPWeak (c : ℕ) {L : Language Bool} (hL : InRP E L) : InRPWeak E c L := by
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  exact ⟨M, a, k, hM, fun x =>
    ⟨fun hx => (min_le_left _ _).trans ((hprop x).1 hx), (hprop x).2⟩⟩

/-- **Error reduction for `RP`** ([AB09, Ex 7.4]): acceptance probability
`min (2/3) ((|x|+1)^{-c})` amplifies to `1 − 2^{-((|x|+1)^d + 1)}` for every `d`, for a model
closed under polynomial `OR`-repetition.

**Proof sketch.** Run the weak verifier on `K = 4(n+1)^{c+d}` independent blocks and accept if
any block accepts (`anyVerifier`).  Non-members are never accepted, since every block is a
genuine random string of the old length.  For members, the run rejects exactly when the vote
count is `0`, which has probability `(1 − s)^K` (`randProb_blockCount`) where `s ≥
(2/3)(n+1)^{-c}` is the single-run acceptance probability; since `2(n+1)^c · s ≥ 1` and
`2(n+1)^c((n+1)^d + 1) ≤ K`, `one_sub_pow_le_half_pow` bounds it by `2^{-((n+1)^d+1)}`. -/
theorem rp_error_reduction (hAny : ClosedUnderAny E) {c : ℕ} {L : Language Bool}
    (hL : InRPWeak E c L) (d : ℕ) : InRPStrong E d L := by
  obtain ⟨M, a, k, hM, hprop⟩ := hL
  refine ⟨anyVerifier M (polyLen a k) (polyLen 4 (c + d)), 4 * a, c + d + k,
    hAny M a k 4 (c + d) hM, fun x => ?_⟩
  have hlen : polyLen (4 * a) (c + d + k) x.length =
      polyLen 4 (c + d) x.length * polyLen a k x.length := by
    unfold polyLen
    ring
  rw [hlen]
  set q := polyLen a k x.length with hq
  set K := polyLen 4 (c + d) x.length with hK
  constructor
  · intro hx
    set s := randProb q (fun l => M x l = true) with hs
    have hs0 : 0 ≤ s := randProb_nonneg
    have hs1 : s ≤ 1 := randProb_le_one
    -- rejection is a zero vote count, of probability `(1 - s)^K`
    have hacc : randProb (K * q)
        (fun l => anyVerifier M (polyLen a k) (polyLen 4 (c + d)) x l = true) =
        1 - (1 - s) ^ K := by
      have h0 := randProb_blockCount q (M x) K 0 (Nat.zero_le _)
      simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul,
        Nat.sub_zero] at h0
      rw [randProb_congr (B := fun l => ¬ (blockCount q K (M x) l = 0)) fun r => by
        simp only [anyVerifier, blockCount, List.any_eq_true, ← Nat.pos_iff_ne_zero,
          List.countP_pos_iff, hq, hK], randProb_not, h0]
    -- the amplification arithmetic
    set y : ℚ := (x.length + 1 : ℚ) ^ c with hy
    have hy1 : 1 ≤ y := one_le_pow₀ (by linarith [(Nat.cast_nonneg x.length : (0:ℚ) ≤ _)])
    have hy0 : 0 < y := by linarith
    have hyinv : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy1
    have hmin : 2/3 * y⁻¹ ≤ s :=
      (le_min (by nlinarith [inv_nonneg.mpr hy0.le]) (by nlinarith [inv_nonneg.mpr hy0.le])).trans
        ((hprop x).1 hx)
    have hm : 1 ≤ ((2 * (x.length + 1) ^ c : ℕ) : ℚ) * s := by
      push_cast
      rw [← hy]
      have : 2 * y * (2/3 * y⁻¹) = 4/3 := by field_simp; ring
      nlinarith
    have he : 2 * (x.length + 1) ^ c * ((x.length + 1) ^ d + 1) ≤ K := by
      have hP : 1 ≤ (x.length + 1) ^ c := Nat.one_le_pow _ _ (Nat.succ_pos _)
      have hQ : 1 ≤ (x.length + 1) ^ d := Nat.one_le_pow _ _ (Nat.succ_pos _)
      rw [hK]
      unfold polyLen
      rw [pow_add]
      nlinarith
    have hpow := one_sub_pow_le_half_pow hs0 hs1 hm he
    rw [hacc]
    linarith
  · intro hx r
    have hl : (List.ofFn r).length = K * q := List.length_ofFn
    unfold anyVerifier
    rw [List.any_eq_false]
    intro i hi
    rw [List.mem_range, ← hK] at hi
    have hiq : i * q + q ≤ K * q := by
      have := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hi)
      rwa [Nat.succ_mul] at this
    have hb : (((List.ofFn r).drop (i * q)).take q).length = q := by
      rw [List.length_take, List.length_drop, hl]
      omega
    obtain ⟨r', hr'⟩ := exists_ofFn_eq hb
    rw [← hq, hr', (hprop x).2 hx r']
    decide

/-- `RP_{n^{-c}} = RP`: the acceptance threshold `2/3` of `RP` may be lowered to an inverse
polynomial. [AB09, p. 133 and Ex 7.4] -/
theorem inRPWeak_iff_inRP (hAny : ClosedUnderAny E) (c : ℕ) (L : Language Bool) :
    InRPWeak E c L ↔ InRP E L :=
  ⟨fun h => (rp_error_reduction E hAny h 0).toInRP E, InRP.toInRPWeak E c⟩

/-- **Error reduction for `RP` over polynomial-time verifiers** ([AB09, Ex 7.4]). -/
theorem rp_error_reduction_polyTime {c : ℕ} {L : Language Bool}
    (hL : InRPWeak polyTimeModel c L) (d : ℕ) : InRPStrong polyTimeModel d L :=
  rp_error_reduction polyTimeModel polyTimeModel_closedUnderAny hL d

end Randomized
