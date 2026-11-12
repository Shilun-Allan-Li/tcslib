/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.Inclusions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The two definitions of BPP agree

[AB09, p. 126] gives an alternative definition of `BPP` (Def 7.3): a deterministic
polynomial-time machine reading its coin tosses as an extra input.  We prove that the PTM
classes of [AB09, Def 7.2 and Def 7.6] (`Randomized.BPP_PTM`, `Randomized.RP_PTM`,
`Randomized.coRP_PTM`) coincide with the certificate classes over polynomial-time verifiers
(`Randomized.InBPP polyTimeModel` etc.), and transfer the certificate-form corollaries.

## Main definitions

* `Turing.FinNDTM.BPDecidesInTimeWith`, `Randomized.BPP_PTMWith`, `Randomized.InBPPWith` —
  `BPP` with success threshold `p(|x|)` in place of `2/3`, PTM and certificate forms.
* `Turing.FinNDTM.RDecidesInTimeWith`, `Randomized.RP_PTMWith` — `RP` with acceptance
  threshold `p(|x|)` in place of `2/3` (the PTM side of [AB09, Ex 7.4]).

## Main results

* `Randomized.randProb_maskSelect` — uniform coins push forward to uniform bits under a
  coordinate projection (with `Randomized.randProb_drop_take` for the slice).
* `Randomized.exists_FinNDTM_maskSelect_of_eff`, `Randomized.exists_FinNDTM_of_eff` — a
  polynomial-time verifier as a PTM reading a coordinate projection of its coins, hence with the
  same output distribution (via `Complexity.exists_maskSelect_host`).
* `Randomized.mem_BPP_PTMWith_iff` — PTM and certificate `BPP` agree at every threshold;
  its `2/3` case `Randomized.mem_BPP_PTM_iff` is `L ∈ BPP ↔ InBPP polyTimeModel L`
  [AB09, Def 7.2 ≡ Def 7.3].
* `Randomized.mem_RP_PTM_iff`, `Randomized.mem_coRP_PTM_iff` — the same for `RP`, `coRP`.
* `Randomized.BPP_PTM_subset_EXP`, `Randomized.BPP_PTM_eq_P_of_P_eq_NP`,
  `Randomized.BPP_PTM_subset_PPoly` [AB09, Thm 7.14],
  `Randomized.BPP_PTM_subset_SigmaP_two_inter_PiP_two` [AB09, Thm 7.15],
  `Randomized.BPP_PTM_of_polyTimeReducible`, `Randomized.PH_eq_SigmaP_two_of_SAT3_mem_BPP_PTM`,
  `Randomized.RP_PTMWith_error_reduction` [AB09, Ex 7.4] — PTM-form corollaries.

## Divergences

* The coin word of a PTM has length exactly its time bound `K·(n^e + 1)`, while a certificate
  verifier draws `polyLen a k n = a·(n+1)^k` bits; the translation pads (coins past halting
  are ignored) or projects onto the coordinates the simulating machine reads.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing

/-! ### Coordinate projections preserve the uniform distribution -/

/-- `maskSelect` returns one bit per marked position. -/
theorem length_maskSelect (mask w : List Bool) (hw : w.length = mask.length) :
    (maskSelect mask w).length = (mask.filter id).length := by
  induction mask generalizing w with
  | nil => cases w <;> rfl
  | cons emit mask ih =>
    cases w with
    | nil => simp at hw
    | cons b w =>
      have ht : w.length = mask.length := by simpa using hw
      cases emit <;> simp [maskSelect, ih w ht]

/-- **Projection onto marked coordinates is measure-preserving**: the bits of a uniform word
at the marked positions of `mask` are uniform. -/
theorem randProb_maskSelect (mask : List Bool) (A : List Bool → Prop) [DecidablePred A] :
    randProb mask.length (fun w => A (maskSelect mask w)) =
      randProb (mask.filter id).length A := by
  induction mask generalizing A with
  | nil =>
    refine randProb_congr fun r => ?_
    have h : List.ofFn r = [] := List.eq_nil_of_length_eq_zero (by simp)
    rw [h]
    rfl
  | cons emit mask ih =>
    rw [List.length_cons, randProb_succ]
    cases emit with
    | false =>
      simp only [maskSelect, if_false, List.nil_append, List.filter_cons, id, Bool.false_eq_true]
      rw [ih A]
      ring
    | true =>
      simp only [maskSelect, if_true, List.singleton_append, List.filter_cons, id,
        List.length_cons]
      rw [ih (fun u => A (false :: u)), ih (fun u => A (true :: u)), randProb_succ]

/-- The slice-then-project map `w ↦ maskSelect mask (w[s, s+|mask|))` pushes the uniform
distribution on `m`-bit words to the uniform distribution on `|mask.filter id|`-bit words. -/
theorem randProb_maskSelect_drop_take {s m : ℕ} (mask : List Bool) (h : s + mask.length ≤ m)
    (A : List Bool → Prop) [DecidablePred A] :
    randProb m (fun w => A (maskSelect mask ((w.drop s).take mask.length))) =
      randProb (mask.filter id).length A := by
  rw [randProb_drop_take h (fun v => A (maskSelect mask v)), randProb_maskSelect]

/-! ### Certificate verifiers from PTMs -/

/-- The indicator of `V` is `true` exactly on `V`. -/
theorem indicator_eq_true_iff {V : Language Bool} {y : List Bool} :
    MultiTapeTM.indicator (V : Set (List Bool)) y = true ↔ y ∈ V := by
  classical
  simp [MultiTapeTM.indicator]

/-- The indicator of `V` is `false` exactly off `V`. -/
theorem indicator_eq_false_iff {V : Language Bool} {y : List Bool} :
    MultiTapeTM.indicator (V : Set (List Bool)) y = false ↔ y ∉ V := by
  classical
  simp [MultiTapeTM.indicator]

/-- A Boolean verifier whose test on `⟨x, r⟩` is a polynomial-time computable bit is
efficient for `polyTimeModel`. -/
theorem eff_boolVerifier_of_test {M : List Bool → List Bool → Bool} {t : List Bool → Bool}
    (ht : PolyTimeComputable fun z => [t z]) (hM : ∀ x r, t (pairEncode x r) = M x r) :
    polyTimeModel.Eff (boolVerifier M) := by
  refine ⟨{z | t z = true}, {z | t z = true}ᶜ, mem_P_of_test ht,
    compl_mem_P (mem_P_of_test ht), fun x r => ?_⟩
  show (some (M x r) = some true ↔ t (pairEncode x r) = true) ∧
    (some (M x r) = some false ↔ ¬ t (pairEncode x r) = true)
  rw [hM]
  simp

/-- A verifier of the form `M(x, r) = [x ++ r ∈ V]` with `V ∈ P` is polynomial-time. -/
theorem eff_append_mem {V : Language Bool} (hV : V ∈ P) :
    polyTimeModel.Eff (boolVerifier fun x r => MultiTapeTM.indicator V (x ++ r)) := by
  classical
  have hg : PolyTimeComputable fun z => pairFstD z ++ pairSndD z :=
    polyTimeComputable_pairFstD.append polyTimeComputable_pairSndD
  have h1 : (fun z => pairFstD z ++ pairSndD z) ⁻¹' V ∈ P := preimage_mem_P hV hg
  refine ⟨_, _, h1, compl_mem_P h1, fun x r => ⟨?_, ?_⟩⟩
  · show some (MultiTapeTM.indicator V (x ++ r)) = some true ↔
      pairFstD (Turing.pairEncode x r) ++ pairSndD (Turing.pairEncode x r) ∈ V
    rw [pairFstD_pairEncode, pairSndD_pairEncode, Option.some.injEq, indicator_eq_true_iff]
  · show some (MultiTapeTM.indicator V (x ++ r)) = some false ↔
      ¬ (pairFstD (Turing.pairEncode x r) ++ pairSndD (Turing.pairEncode x r) ∈ V)
    rw [pairFstD_pairEncode, pairSndD_pairEncode, Option.some.injEq, indicator_eq_false_iff]

/-- The choice-word verifier of a PTM `N` halting within `T ≤ Q` steps on `x`: on a `Q`-bit
coin word `r`, it accepts iff `N` outputs `[true]` under the first `T` coins of `r`. -/
theorem append_mem_iff_outputWith_take {N : FinNDTM Bool} {V : Language Bool} {x : List Bool}
    {T Q : ℕ}
    (hV : ∀ u : List Bool, u.length = Q →
      (x ++ u ∈ V ↔ (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true]))
    (hhalt : N.tm.HaltsWithin x T) (hTQ : T ≤ Q) (r : List Bool) (hr : r.length = Q) :
    x ++ r ∈ V ↔ N.outputWith x (r.take T) = [true] := by
  have hle : T ≤ r.length := hr ▸ hTQ
  rw [hV r hr, FinNDTM.runWith_eq_runWith_take hhalt hle]
  exact ⟨fun h => h.2, fun h => ⟨hhalt _ (List.length_take_of_le hle), h⟩⟩

/-- The acceptance probability of the choice-word verifier is the PTM's. -/
theorem randProb_choiceVerifier {N : FinNDTM Bool} {V : Language Bool} {x : List Bool}
    {T Q : ℕ}
    (hV : ∀ u : List Bool, u.length = Q →
      (x ++ u ∈ V ↔ (N.tm.runWith u (N.tm.initCfg x)).state = none ∧
        (N.tm.runWith u (N.tm.initCfg x)).output = [true]))
    (hhalt : N.tm.HaltsWithin x T) (hTQ : T ≤ Q) :
    (randProb Q fun r => MultiTapeTM.indicator V (x ++ r) = true) = N.outputProb x T [true] := by
  classical
  unfold FinNDTM.outputProb
  rw [← randProb_take hTQ fun w => N.outputWith x w = [true]]
  refine randProb_congr fun r => ?_
  rw [indicator_eq_true_iff]
  exact append_mem_iff_outputWith_take hV hhalt hTQ _ (List.length_ofFn)

end Randomized

/-! ### `BPP` with a general success threshold -/

namespace Turing.FinNDTM

/-- `N` decides `L` in time `T` with success threshold `p(|x|)`: every branch halts within
`T(|x|)` steps and `Pr[N(x) = L(x)] ≥ p(|x|)`. [AB09, Def 7.2 and Lemma 7.9] -/
def BPDecidesInTimeWith (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) (p : ℕ → ℚ) :
    Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length) ∧
    p x.length ≤ N.outputProb x (T x.length) [MultiTapeTM.indicator (L : Set (List Bool)) x]

/-- `BPDecidesInTime` is the threshold-`2/3` case. -/
theorem bpDecidesInTime_iff_with {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ} :
    N.BPDecidesInTime L T ↔ N.BPDecidesInTimeWith L T fun _ => 2/3 := Iff.rfl

end Turing.FinNDTM

namespace Randomized

open Complexity Turing

/-- `BPP` with success threshold `p(|x|)`: bounded-error PTMs in time `K·(n^e + 1)`.
[AB09, Lemma 7.9] -/
def BPP_PTMWith (p : ℕ → ℚ) : Set (Language Bool) :=
  ⋃ e : ℕ, {L | ∃ (K : ℕ) (N : FinNDTM Bool),
    N.BPDecidesInTimeWith L (fun n => K * (n ^ e + 1)) p}

/-- `BPP_PTM` is the threshold-`2/3` case. -/
theorem BPP_PTM_eq_BPP_PTMWith : BPP_PTM = BPP_PTMWith fun _ => 2/3 := rfl

/-- The certificate form of `BPP_PTMWith p` over polynomial-time verifiers. -/
def InBPPWith (p : ℕ → ℚ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    polyTimeModel.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → p x.length ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → p x.length ≤ randProb (polyLen a k x.length) fun r => M x r = false)

/-- `InBPP polyTimeModel` is the threshold-`2/3` case. -/
theorem inBPPWith_iff_inBPP (L : Language Bool) :
    InBPPWith (fun _ => 2/3) L ↔ InBPP polyTimeModel L := Iff.rfl

/-- **Def 7.2 ⇒ Def 7.3 at threshold `p`**: a polynomial-time PTM yields a polynomial-time
verifier reading its coins as the random string. [AB09, p. 126]

**Proof sketch.** If `N` runs in time `T(n) = c(n^e + 1)`, take `M(x, r) = [x ++ r ∈ V]` with
`V` the choice-word verifier of `exists_choiceVerifier_mem_P` at length `Q = 2c(n+1)^e ≥ T`
(`choiceBudget_le`).  On a `Q`-bit word, `M` accepts iff `N` outputs `[true]` under its first
`T` coins (`append_mem_iff_outputWith_take`), so `randProb_take` turns `Pr[M = 1]` into
`Pr[N(x) = 1]`, and `Pr[M = 0] ≥ Pr[N(x) = 0]`. -/
theorem inBPPWith_of_mem_BPP_PTMWith {p : ℕ → ℚ} {L : Language Bool}
    (h : L ∈ BPP_PTMWith p) : InBPPWith p L := by
  classical
  obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
  obtain ⟨V, hVP, hV⟩ := exists_choiceVerifier_mem_P N (2 * c) e
  refine ⟨fun x r => MultiTapeTM.indicator V (x ++ r), 2 * c, e, eff_append_mem hVP, fun x => ?_⟩
  obtain ⟨hhalt, hprob⟩ := hN x
  have hTQ : c * (x.length ^ e + 1) ≤ polyLen (2 * c) e x.length := choiceBudget_le c e _
  have hVx : ∀ u : List Bool, u.length = polyLen (2 * c) e x.length → _ := fun u => hV x u
  have htrue := randProb_choiceVerifier hVx hhalt hTQ
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · exact le_of_le_of_eq (by simpa [MultiTapeTM.indicator, hx] using hprob) htrue.symm
  · have hfalse : N.outputProb x (c * (x.length ^ e + 1)) [false] ≤
        randProb (polyLen (2 * c) e x.length)
          fun r => MultiTapeTM.indicator V (x ++ r) = false := by
      unfold FinNDTM.outputProb
      rw [← randProb_take hTQ fun w => N.outputWith x w = [false]]
      refine randProb_mono fun r hr => ?_
      rw [indicator_eq_false_iff,
        append_mem_iff_outputWith_take hVx hhalt hTQ _ List.length_ofFn, hr]
      decide
    refine le_trans ?_ hfalse
    simpa [MultiTapeTM.indicator, hx] using hprob

/-- **Def 7.2 ⇒ Def 7.3** (`BPP`), the threshold-`2/3` case of
`inBPPWith_of_mem_BPP_PTMWith`. [AB09, p. 126] -/
theorem inBPP_of_mem_BPP_PTM {L : Language Bool} (h : L ∈ BPP_PTM) :
    InBPP polyTimeModel L :=
  inBPPWith_of_mem_BPP_PTMWith (p := fun _ => 2/3) h

/-! ### PTMs from certificate verifiers -/

/-- **Def 7.3 ⇒ Def 7.2, the machine structure**: a polynomial-time verifier `M` with
`polyLen a k` random bits is simulated by a PTM running in time `K·(n^e + 1)` whose output on a
coin word `w` is `[M(x, u)]`, `u` the projection of the slice `w[s, s + |mask|)` onto the
`polyLen a k |x|` marked positions of `mask` (so `|u| = polyLen a k |x|`).

**Proof sketch.** Let `V = {y | y = x ++ u, |u| = a(|x|+1)^k, ⟨x, u⟩ ∈ V₁} ∈ P`, recovered by
`computesFunInTime_splitSolve`; `exists_maskSelect_host` gives a PTM whose verdict is `V(x ++ u)`
with `u` such a projection. -/
theorem exists_FinNDTM_maskSelect_of_eff {M : List Bool → List Bool → Bool} {a k : ℕ}
    (hM : polyTimeModel.Eff (boolVerifier M)) :
    ∃ (K e : ℕ) (N : FinNDTM Bool), ∀ x : List Bool, ∃ (s : ℕ) (mask : List Bool),
      (mask.filter id).length = polyLen a k x.length ∧
      s + mask.length ≤ K * (x.length ^ e + 1) ∧
      ∀ w : List Bool, w.length = K * (x.length ^ e + 1) →
        (N.tm.runWith w (N.tm.initCfg x)).state = none ∧
        N.outputWith x w = [M x (maskSelect mask ((w.drop s).take mask.length))] ∧
        (maskSelect mask ((w.drop s).take mask.length)).length = polyLen a k x.length := by
  classical
  obtain ⟨V₁, V₀, hV₁, -, hMV⟩ := hM
  let sp : List Bool → List Bool := fun w => match solveSplit a k w.length with
    | some i => Turing.pairEncode (w.take i) (w.drop i)
    | none => []
  have hsp : PolyTimeComputable sp := by
    obtain ⟨S, c, hS⟩ := FinTM.computesFunInTime_splitSolve a k
    exact ⟨S, c, k + 2, hS⟩
  have hVP : sp ⁻¹' V₁ ∈ P := preimage_mem_P hV₁ hsp
  have hsplit : ∀ x u : List Bool, u.length = polyLen a k x.length →
      MultiTapeTM.indicator (sp ⁻¹' V₁) (x ++ u) = M x u := by
    intro x u hu
    have hs : sp (x ++ u) = Turing.pairEncode x u := by
      simp only [sp, List.length_append, hu, polyLen, Meyer.solveSplit_self', List.take_left',
        List.drop_left']
    have hiff : M x u = true ↔ Turing.pairEncode x u ∈ V₁ := by
      simpa only [boolVerifier, Option.some.injEq] using (hMV x u).1
    cases hb : M x u
    · have : x ++ u ∉ sp ⁻¹' V₁ := by
        rw [Set.mem_preimage, hs, ← hiff, hb]
        decide
      simp [MultiTapeTM.indicator, this]
    · have : x ++ u ∈ sp ⁻¹' V₁ := by rw [Set.mem_preimage, hs, ← hiff, hb]
      simp [MultiTapeTM.indicator, this]
  obtain ⟨K, e, N, hN⟩ := exists_maskSelect_host (sp ⁻¹' V₁) hVP a k
  refine ⟨K, e, N, fun x => ?_⟩
  obtain ⟨s, mask, hcount, hle, hrun⟩ := hN x
  have hsel : ∀ w : List Bool, w.length = K * (x.length ^ e + 1) →
      (maskSelect mask ((w.drop s).take mask.length)).length = polyLen a k x.length := by
    intro w hw
    rw [length_maskSelect _ _ (List.length_take_of_le (by rw [List.length_drop]; omega)),
      hcount]
    rfl
  refine ⟨s, mask, hcount, hle, fun w hw => ⟨(hrun w hw).1, ?_, hsel w hw⟩⟩
  rw [FinNDTM.outputWith, (hrun w hw).2, hsplit x _ (hsel w hw)]

/-- **Def 7.3 ⇒ Def 7.2, the machine**: a polynomial-time verifier `M` with `polyLen a k`
random bits is simulated by a PTM running in time `K·(n^e + 1)` whose output on every branch
is `[M(x, u)]` for a `polyLen a k |x|`-bit word `u`, and whose output distribution is that of
`M(x, ·)`.

**Proof sketch.** The machine of `exists_FinNDTM_maskSelect_of_eff`; a coordinate projection of
a slice of uniform coins is uniform (`randProb_maskSelect_drop_take`). -/
theorem exists_FinNDTM_of_eff {M : List Bool → List Bool → Bool} {a k : ℕ}
    (hM : polyTimeModel.Eff (boolVerifier M)) :
    ∃ (K e : ℕ) (N : FinNDTM Bool), ∀ x : List Bool,
      N.tm.HaltsWithin x (K * (x.length ^ e + 1)) ∧
      (∀ b : Bool, N.outputProb x (K * (x.length ^ e + 1)) [b] =
        randProb (polyLen a k x.length) fun u => M x u = b) ∧
      ∀ w : List Bool, w.length = K * (x.length ^ e + 1) →
        ∃ r : Fin (polyLen a k x.length) → Bool, N.outputWith x w = [M x (List.ofFn r)] := by
  classical
  obtain ⟨K, e, N, hN⟩ := exists_FinNDTM_maskSelect_of_eff (a := a) (k := k) hM
  refine ⟨K, e, N, fun x => ?_⟩
  obtain ⟨s, mask, hcount, hle, hrun⟩ := hN x
  refine ⟨fun w hw => (hrun w hw).1, fun b => ?_, fun w hw => ?_⟩
  · unfold FinNDTM.outputProb
    rw [randProb_congr (B := fun w => M x (maskSelect mask ((w.drop s).take mask.length)) = b)
      fun r => by rw [(hrun _ List.length_ofFn).2.1, List.singleton_inj]]
    refine (randProb_maskSelect_drop_take mask hle (fun u => M x u = b)).trans ?_
    rw [hcount]
  · obtain ⟨r, hr⟩ := exists_ofFn_eq (hrun w hw).2.2
    exact ⟨r, by rw [(hrun w hw).2.1, hr]⟩

/-- **Def 7.3 ⇒ Def 7.2 at threshold `p`.** [AB09, p. 126] -/
theorem mem_BPP_PTMWith_of_inBPPWith {p : ℕ → ℚ} {L : Language Bool}
    (h : InBPPWith p L) : L ∈ BPP_PTMWith p := by
  classical
  obtain ⟨M, a, k, hM, hL⟩ := h
  obtain ⟨K, e, N, hN⟩ := exists_FinNDTM_of_eff (a := a) (k := k) hM
  refine Set.mem_iUnion.mpr ⟨e, K, N, fun x => ⟨(hN x).1, ?_⟩⟩
  rw [(hN x).2.1]
  by_cases hx : x ∈ L
  · simpa [MultiTapeTM.indicator, hx] using (hL x).1 hx
  · simpa [MultiTapeTM.indicator, hx] using (hL x).2 hx

/-- **PTM and certificate `BPP` agree at every threshold.** [AB09, Def 7.2 ≡ Def 7.3] -/
theorem mem_BPP_PTMWith_iff (p : ℕ → ℚ) (L : Language Bool) :
    L ∈ BPP_PTMWith p ↔ InBPPWith p L :=
  ⟨inBPPWith_of_mem_BPP_PTMWith, mem_BPP_PTMWith_of_inBPPWith⟩

/-- **Def 7.3 ⇒ Def 7.2** (`BPP`), the threshold-`2/3` case of
`mem_BPP_PTMWith_of_inBPPWith`. [AB09, p. 126] -/
theorem mem_BPP_PTM_of_inBPP {L : Language Bool} (h : InBPP polyTimeModel L) :
    L ∈ BPP_PTM :=
  mem_BPP_PTMWith_of_inBPPWith (p := fun _ => 2/3) h

/-- **[AB09, Def 7.2 ≡ Def 7.3]**: the PTM class `BPP` is the certificate class over
polynomial-time verifiers. -/
theorem mem_BPP_PTM_iff (L : Language Bool) : L ∈ BPP_PTM ↔ InBPP polyTimeModel L :=
  mem_BPP_PTMWith_iff (fun _ => 2/3) L

/-- `BPP_PTM` as a set of languages. -/
theorem BPP_PTM_eq : BPP_PTM = {L | InBPP polyTimeModel L} :=
  Set.ext mem_BPP_PTM_iff

end Randomized

/-! ### `RP` with a general acceptance threshold -/

namespace Turing.FinNDTM

/-- `N` decides `L` in time `T` with one-sided error and acceptance threshold `p(|x|)`: every
branch halts within `T(|x|)` steps, members are accepted with probability at least `p(|x|)`,
and on non-members every branch outputs `0`. The threshold `p` is meant to be positive (at
`p = 0` every language qualifies). [AB09, Def 7.6 and Ex 7.4] -/
def RDecidesInTimeWith (N : FinNDTM Bool) (L : Language Bool) (T : ℕ → ℕ) (p : ℕ → ℚ) :
    Prop :=
  ∀ x : List Bool, N.tm.HaltsWithin x (T x.length) ∧
    (x ∈ L → p x.length ≤ N.outputProb x (T x.length) [true]) ∧
    (x ∉ L → ∀ w : List Bool, w.length = T x.length → N.outputWith x w = [false])

/-- `RDecidesInTime` is the threshold-`2/3` case. -/
theorem rDecidesInTime_iff {N : FinNDTM Bool} {L : Language Bool} {T : ℕ → ℕ} :
    N.RDecidesInTime L T ↔ N.RDecidesInTimeWith L T fun _ => 2/3 := Iff.rfl

end Turing.FinNDTM

namespace Randomized

open Complexity Turing

/-- `RP` with acceptance threshold `p(|x|)` (meant positive): one-sided-error PTMs in time
`K·(n^e + 1)`. [AB09, Ex 7.4] -/
def RP_PTMWith (p : ℕ → ℚ) : Set (Language Bool) :=
  ⋃ e : ℕ, {L | ∃ (K : ℕ) (N : FinNDTM Bool),
    N.RDecidesInTimeWith L (fun n => K * (n ^ e + 1)) p}

/-- `RP_PTM` is the threshold-`2/3` case. -/
theorem RP_PTM_eq_RP_PTMWith : RP_PTM = RP_PTMWith fun _ => 2/3 := rfl

/-- The certificate form of `RP_PTMWith p` over polynomial-time verifiers. -/
def InRPWith (p : ℕ → ℚ) (L : Language Bool) : Prop :=
  ∃ (M : List Bool → List Bool → Bool) (a k : ℕ),
    polyTimeModel.Eff (boolVerifier M) ∧
    ∀ x : List Bool,
      (x ∈ L → p x.length ≤ randProb (polyLen a k x.length) fun r => M x r = true) ∧
      (x ∉ L → ∀ r : Fin (polyLen a k x.length) → Bool, M x (List.ofFn r) = false)

/-- **PTM and certificate `RP` agree at every threshold.** [AB09, Def 7.6, p. 131]

**Proof sketch.** Forward as `inBPPWith_of_mem_BPP_PTMWith`; a non-member's coin word outputs
`[false]` under its first `T` coins, so the verifier rejects it.  Backward by
`exists_FinNDTM_of_eff`: every branch outputs `[M(x, u)]` for some `polyLen a k |x|`-bit `u`,
which is `0` on non-members, and the acceptance probabilities agree. -/
theorem mem_RP_PTMWith_iff (p : ℕ → ℚ) (L : Language Bool) :
    L ∈ RP_PTMWith p ↔ InRPWith p L := by
  classical
  constructor
  · intro h
    obtain ⟨e, c, N, hN⟩ := Set.mem_iUnion.mp h
    obtain ⟨V, hVP, hV⟩ := exists_choiceVerifier_mem_P N (2 * c) e
    refine ⟨fun x r => MultiTapeTM.indicator V (x ++ r), 2 * c, e, eff_append_mem hVP, fun x => ?_⟩
    obtain ⟨hhalt, hin, hout⟩ := hN x
    have hTQ : c * (x.length ^ e + 1) ≤ polyLen (2 * c) e x.length := choiceBudget_le c e _
    have hVx : ∀ u : List Bool, u.length = polyLen (2 * c) e x.length → _ := fun u => hV x u
    refine ⟨fun hx => le_of_le_of_eq (hin hx) (randProb_choiceVerifier hVx hhalt hTQ).symm,
      fun hx r => ?_⟩
    rw [indicator_eq_false_iff, append_mem_iff_outputWith_take hVx hhalt hTQ _ List.length_ofFn,
      hout hx _ (List.length_take_of_le (by rw [List.length_ofFn]; exact hTQ))]
    decide
  · rintro ⟨M, a, k, hM, hL⟩
    obtain ⟨K, e, N, hN⟩ := exists_FinNDTM_of_eff (a := a) (k := k) hM
    refine Set.mem_iUnion.mpr ⟨e, K, N, fun x => ⟨(hN x).1, fun hx => ?_, fun hx w hw => ?_⟩⟩
    · rw [(hN x).2.1]
      exact (hL x).1 hx
    · obtain ⟨r, hr⟩ := (hN x).2.2 w hw
      rw [hr, (hL x).2 hx r]

/-- **[AB09, Def 7.6]**: the PTM class `RP` is the certificate class over polynomial-time
verifiers. -/
theorem mem_RP_PTM_iff (L : Language Bool) : L ∈ RP_PTM ↔ InRP polyTimeModel L := by
  rw [RP_PTM_eq_RP_PTMWith]
  exact mem_RP_PTMWith_iff _ L

/-- **[AB09, §7.3]**: the PTM class `coRP` is the certificate class over polynomial-time
verifiers. -/
theorem mem_coRP_PTM_iff (L : Language Bool) : L ∈ coRP_PTM ↔ InCoRP polyTimeModel L :=
  mem_RP_PTM_iff Lᶜ

/-! ### PTM-form corollaries -/

/-- **`BPP ⊆ EXP`** (PTM form). [AB09, p. 126] -/
theorem BPP_PTM_subset_EXP : BPP_PTM ⊆ EXP := fun _ h =>
  mem_EXP_of_inBPP_polyTimeModel (inBPP_of_mem_BPP_PTM h)

/-- **`P = NP ⇒ BPP = P`** (PTM form). [AB09, p. 135 and p. 140] -/
theorem BPP_PTM_eq_P_of_P_eq_NP (h : P = NP) : BPP_PTM = P :=
  Set.ext fun L => (mem_BPP_PTM_iff L).trans (inBPP_polyTimeModel_iff_mem_P_of_P_eq_NP h L)

/-- **Adleman: `BPP ⊆ P/poly`** (PTM form). [AB09, Thm 7.14] -/
theorem BPP_PTM_subset_PPoly : BPP_PTM ⊆ BoolCircuit.PPoly := fun L h =>
  (BoolCircuit.mem_PPoly_iff L).mpr (adleman_polyTime (inBPP_of_mem_BPP_PTM h))

/-- **Sipser–Gács: `BPP ⊆ Σ₂ᵖ ∩ Π₂ᵖ`** (PTM form). [AB09, Thm 7.15] -/
theorem BPP_PTM_subset_SigmaP_two_inter_PiP_two : BPP_PTM ⊆ SigmaP 2 ∩ PiP 2 := fun _ h =>
  sipser_gacs_polyTime (inBPP_of_mem_BPP_PTM h)

/-- **`BPP` is closed under `≤ₚ`** (PTM form). -/
theorem BPP_PTM_of_polyTimeReducible {L L' : Language Bool} (hred : L' ≤ₚ L)
    (h : L ∈ BPP_PTM) : L' ∈ BPP_PTM :=
  mem_BPP_PTM_of_inBPP (InBPP.of_polyTimeReducible hred (inBPP_of_mem_BPP_PTM h))

/-- **`3SAT ∈ BPP ⇒ PH = Σ₂ᵖ`** (PTM form). [AB09, p. 135] -/
theorem PH_eq_SigmaP_two_of_SAT3_mem_BPP_PTM (h : SAT3 ∈ BPP_PTM) : PH = SigmaP 2 :=
  PH_eq_SigmaP_two_of_inBPP_SAT3 (inBPP_of_mem_BPP_PTM h)

/-- **Error reduction for `RP`** (PTM form, [AB09, Ex 7.4]): a polynomial-time PTM accepting
members with probability `min (2/3) ((|x|+1)^{-c})` yields one accepting them with probability
`1 − 2^{-((|x|+1)^d + 1)}`. -/
theorem RP_PTMWith_error_reduction (c d : ℕ) :
    RP_PTMWith (fun n => min (2/3) (((n + 1 : ℚ) ^ c)⁻¹)) ⊆
      RP_PTMWith fun n => 1 - (1/2 : ℚ) ^ ((n + 1) ^ d + 1) := fun L h =>
  (mem_RP_PTMWith_iff _ L).mpr
    (rp_error_reduction_polyTime (c := c) ((mem_RP_PTMWith_iff _ L).mp h) d)

end Randomized
