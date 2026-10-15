/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Machine
import TCSlib.Complexity.SpaceComplexity.Machines.VWord

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Runs of the codec machine's loops

Each loop family of the codec machine `Complexity.Codec.CA` (copies, scales, increment chains,
decodings, the parse scans, the width check, the two scans) runs as the corresponding shared
fragment says (`Complexity.LogProg.registerCopy_loop`, `registerScale_loop`,
`alignedPair_loop`, `canonicalTail_loop`, `inputLength_loop`, and the fragments of
`TCSlib.Complexity.SpaceComplexity.Codec.Engine`). The lemmas here instantiate them once per
family, for every instance and every mode, against the input oracles.

Logspace machine infrastructure for the codec; not a result of [AB09].

## Main definitions

* `Complexity.Codec.codecAs`, `Complexity.Codec.orc` — the two oracle languages and the
  oracle they answer.

## Main results

* `Complexity.Codec.orc_bit`, `Complexity.Codec.orc_len` — the oracle reads the input.
* `Complexity.Codec.cp_run`, `sc_run`, `ic_run`, `dc_run`, `pr_run`, `ct_run`, `len_run`,
  `hc_run`, `le_run`, `v_run`, `s_run` — the loop families.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.)
-/

namespace Complexity.Codec

open Turing LogProg

/-- The oracle languages: the length and the bit language of the input. -/
def codecAs : Fin 2 → Language Bool := fun j => if j = 0 then inputLenLang else inputBitLang

/-- The oracle languages are logspace. -/
lemma codecAs_mem (j : Fin 2) : codecAs j ∈ LOGSPACE := by
  fin_cases j
  · exact inputLenLang_mem
  · exact inputBitLang_mem

/-- The oracle answering the codec machine's calls. -/
noncomputable def orc : Fin 2 → List Bool → Bool :=
  fun j V => MultiTapeTM.indicator (codecAs j : Set (List Bool)) V

/-- The bit oracle reads the input. -/
lemma orc_bit (y : List Bool) (a : ℕ) : orc jBit (pairEncode y (Nat.bits a)) = y.getD a false := by
  show MultiTapeTM.indicator (inputBitLang : Set (List Bool)) _ = _
  exact indicator_inputBitLang y a

/-- The length oracle compares with the input length. -/
lemma orc_len (y : List Bool) (a : ℕ) :
    orc jLen (pairEncode y (Nat.bits a)) = decide (a < y.length) := by
  show MultiTapeTM.indicator (inputLenLang : Set (List Bool)) _ = _
  exact indicator_inputLenLang y a

variable {N : FinNDTM Bool} {mode : CMode}

/-- Runs of the codec machine through bounded configurations. -/
abbrev Reach (N : FinNDTM Bool) (mode : CMode) (y : List Bool) (B : ℕ)
    (l : Lab N) (v : Fin 21 → ℕ) (l' : Lab N) (v' : Fin 21 → ℕ) : Prop :=
  AReach (CA N mode) orc y (GuardLe (CA N mode) y B) (some l, v, none) (some l', v', none)

/-- Runs compose. -/
lemma Reach.trans {y : List Bool} {B : ℕ} {l₁ l₂ l₃ : Lab N} {v₁ v₂ v₃ : Fin 21 → ℕ}
    (h₁ : Reach N mode y B l₁ v₁ l₂ v₂) (h₂ : Reach N mode y B l₂ v₂ l₃ v₃) :
    Reach N mode y B l₁ v₁ l₃ v₃ := AReach.trans h₁ h₂

/-- A run to an equal valuation. -/
lemma Reach.cast {y : List Bool} {B : ℕ} {l₁ l₂ : Lab N} {v₁ v₂ v₂' : Fin 21 → ℕ}
    (h : Reach N mode y B l₁ v₁ l₂ v₂) (e : v₂ = v₂') : Reach N mode y B l₁ v₁ l₂ v₂' := e ▸ h

/-- One step of the machine as a run. -/
lemma Reach.single' {y : List Bool} {B : ℕ} {l l' : Lab N} {v v' : Fin 21 → ℕ}
    (hG : GuardLe (CA N mode) y B (some l, v, none))
    (e : astep (CA N mode) orc y (some l, v, none) = (some l', v', none)) :
    Reach N mode y B l v l' v' := by
  have := AReach.single (A := CA N mode) (oracle := orc) (x := y) hG
  rwa [e] at this

/-- The guard at a label that is not a register comparison or a call. -/
lemma gd_of {y : List Bool} {B : ℕ} {l : Lab N} {v : Fin 21 → ℕ} (hv : ∀ r, v r ≤ B)
    (h : PreS (CA N mode) y (some l, v, none)) : GuardLe (CA N mode) y B (some l, v, none) :=
  ⟨h, hv⟩

/-! ## Copies, scales, increment chains -/

/-- Copy loops copy between distinct registers. -/
lemma cpDst_ne (c : CpId) : cpDst c ≠ cpSrc c := by cases c <;> decide

/-- **Copy loops**: the destination counts up to the source. -/
theorem cp_run (y : List Bool) (B : ℕ) (c : CpId) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hle : v (cpDst c) ≤ v (cpSrc c)) :
    Reach N mode y B (.cp c) v (cpNext N c) (Function.update v (cpDst c) (v (cpSrc c))) :=
  registerCopy_loop (CA N mode) orc y (cpDst c) (cpSrc c) (cpDst_ne c) (.cp c) (.cpI c)
    (cpNext N c) rfl rfl B v hv hle

/-- Scale loops scale between distinct registers. -/
lemma scSrc_ne (c : ScId) : scSrc c ≠ scDst c := by cases c <;> decide

/-- **Scale loops**: `dst += factor · src`, clearing `src`. -/
theorem sc_run (y : List Bool) (B : ℕ) (c : ScId) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (htot : v (scDst c) + scFactor N c * v (scSrc c) ≤ B) :
    Reach N mode y B (.sc c) v (scNext N c)
      (Function.update (Function.update v (scSrc c) 0) (scDst c)
        (v (scDst c) + scFactor N c * v (scSrc c))) := by
  refine registerScale_loop (CA N mode) orc y (scSrc c) (scDst c) (scSrc_ne c) (.sc c)
    (.scDown c) (scNext N c) (scIncs N c) (scFactor N c) rfl rfl (fun i hi => ?_) ?_ B v hv htot
  · simp only [scIncs, dif_pos hi]; rfl
  · simp [scIncs]

/-- **Increment chains**. -/
theorem ic_run (y : List Bool) (B : ℕ) (c : IcId) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hk : v (icReg c) + icCount N c ≤ B) :
    Reach N mode y B (icL N c 0) v (icNext N c)
      (Function.update v (icReg c) (v (icReg c) + icCount N c)) := by
  have h := incChain (CA N mode) orc y (icReg c) (icL N c) (icCount N c) B (fun i hi => by
    simp only [icL, dif_pos hi]; rfl) v hv hk
  simpa [icL] using h

/-- The first label of an increment chain. -/
lemma icL_zero (c : IcId) : icL N c 0 = .ic c ⟨0, by have := icCount_le N c; simp [W]⟩ := by
  have : 0 < icCount N c := by cases c <;> simp [icCount, W]
  simp [icL, this]

/-! ## Decodings -/

/-- Pointer, base, accumulator, temporary of a decoding are distinct. -/
lemma dc_distinct (c : DcId) : dcPtr c ≠ dcBase c ∧ dcPtr c ≠ dcAcc c ∧ dcPtr c ≠ rT ∧
    dcBase c ≠ dcAcc c ∧ dcBase c ≠ rT ∧ dcAcc c ≠ rT := by
  cases c <;> decide

/-- **Decoding loops**: from the pointer `stride · |w|` above the base, with the accumulator
and the temporary cleared, the run ends with the accumulator holding the value of the field
`w` read at the stride, the pointer at the base, the temporary cleared.

**Proof sketch.** `decodeStride_loop` at the instance's registers and labels, from the top of
the field; its frame conditions identify the final valuation. -/
theorem dc_run (y : List Bool) (B : ℕ) (c : DcId) (w : List Bool)
    (values : ∀ i ≤ w.length, bitsVal (w.drop i) ≤ B) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hp : v (dcPtr c) = v (dcBase c) + dcStride c * w.length) (ha : v (dcAcc c) = 0)
    (ht : v rT = 0)
    (ho : ∀ i < w.length,
      y.getD (v (dcBase c) + dcStride c * i) false = w.getD i false) :
    Reach N mode y B (.dcTest c) v (dcNext N c)
      (Function.update (Function.update v (dcPtr c) (v (dcBase c))) (dcAcc c) (bitsVal w)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := dc_distinct c
  have hs : 0 < dcStride c := by cases c <;> simp [dcStride]
  obtain ⟨v', bv, ep, ea, et, frame, run⟩ := decodeStride_loop (CA N mode) orc y (dcPtr c)
    (dcBase c) (dcAcc c) rT h1 h2 h3 h4 h5 h6 jBit (.dcTest c) (.dcRead c) (dcNext N c)
    (dcDowns N c) (.dcCopy c) (.dcBump c) (.dcClear c) (.dcScale c) (.dcTake c) (.dcAdd c)
    (dcIncs N c) (dcStride c) rfl (fun i hi => by simp only [dcDowns, dif_pos hi]; rfl)
    (by simp [dcDowns]) rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun b i hi => by simp only [dcIncs, dif_pos hi]; rfl)
    (fun b => by simp [dcIncs]) (fun b => by cases b <;> rfl) w B values w.length le_rfl v hv hs
    hp (by rw [ha, List.drop_length]; rfl) ht (fun i hi => by rw [orc_bit]; exact ho i hi)
  refine Reach.cast run (funext fun r => ?_)
  by_cases hrp : r = dcPtr c
  · subst hrp; simp [ep, h2]
  · by_cases hra : r = dcAcc c
    · subst hra; simp [ea]
    · by_cases hrt : r = rT
      · subst hrt; simp [et, hrp, hra, ht]
      · simp [frame r hrp hra hrt, hrp, hra]

/-! ## Measuring, parsing, checking widths -/

/-- **Measuring the input**: the length loop counts `rL` up to `|y|`. -/
theorem len_run (y : List Bool) (B : ℕ) (hB : y.length ≤ B) (v : Fin 21 → ℕ)
    (hv : ∀ r, v r ≤ B) (hr : v rL ≤ y.length) :
    Reach N mode y B .lenScan v (.prScan 0) (Function.update v rL y.length) :=
  inputLength_loop (CA N mode) orc y rL jLen .lenScan .lenInc (.prScan 0) rfl rfl
    (fun n _ => orc_len y n) B hB v hv hr

/-- **Parse loops**: from `rP = a`, the aligned pair scan of the suffix `y.drop a` rejects a
suffix that is not a pair, and otherwise ends past the first component and the separator. -/
theorem pr_run (y : List Bool) (B : ℕ) (p : Fin 3) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hL : v rL = y.length) (ha : v rP ≤ y.length) :
    match pairDecode (y.drop (v rP)) with
    | none => ∃ t ≤ (y.drop (v rP)).length,
        Reach N mode y B (.prScan p) v .rej (Function.update v rP (v rP + 1 * t))
    | some (u, _) => Reach N mode y B (.prScan p) v (prCont N mode p 3)
        (Function.update v rP (v rP + 1 * (2 * u.length + 2))) :=
  alignedPair_loop (CA N mode) orc y rP rL jBit (.prScan p) (.prFirst p) (.prTest p)
    (.prRead p) .rej (prCont N mode p 3) (prAdvL N mode p) 1 B (by omega) (by decide)
    rfl rfl (fun _ => rfl) (fun _ => rfl)
    (fun k i hi => by obtain rfl : i = 0 := by omega
                      rfl)
    (by simp only [prAdvL, one_ne_zero, ↓reduceIte]; exact ⟨rfl, rfl, rfl, trivial⟩)
    (y.drop (v rP)) v hv (by simp [hL]; omega)
    (fun i hi => by rw [orc_bit, getD_drop]; ring_nf)

/-- **The width check** of the radius field: from `rQ1` at the start of the last field `w`
of the input, with the cap `rCap`, the run reaches the radius decoding exactly when `w` is
canonical and has at most `|bits (rCap)|` letters; otherwise it rejects. -/
theorem ct_run (y : List Bool) (B : ℕ) (w : List Bool) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hl : v rL = v rQ1 + 1 * w.length)
    (ho : ∀ i < w.length, y.getD (v rQ1 + 1 * i) false = w.getD i false) :
    ∃ v', (∀ r, v' r ≤ B) ∧ v' rQ1 ≤ v rL ∧ (∀ r, r ≠ rQ1 → r ≠ rCap → v' r = v r) ∧
      Reach N mode y B (.ctTest true) v
        (if w.length ≤ (Nat.bits (v rCap)).length then
          if w.getLastD true then .cp .Q2 else .rej else .rej) v' := by
  obtain ⟨v', h1, h2, h3, h4⟩ := canonicalTail_loop (CA N mode) orc y rQ1 rL rCap (by decide)
    (by decide) (by decide) jBit .ctTest .ctCheck .ctRead .rej (.cp .Q2) .ctHalve
    (fun b i => if i = 0 then .ctAdv b else .ctTest b) 1 B (by omega) (fun _ => rfl) rfl rfl
    (fun _ => rfl) (fun b i hi => by obtain rfl : i = 0 := by omega
                                     rfl)
    (fun b => by simp) w true v hv hl (fun i hi => by rw [orc_bit]; exact ho i hi)
  exact ⟨v', h1, h2, h3, h4⟩

/-- **Counting the position width**: halving a copy of `n + 1` in `rT` while counting in
`rWp`. -/
theorem hc_run (y : List Bool) (B : ℕ) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hc : v rWp + (Nat.bits (v rT)).length ≤ B) :
    Reach N mode y B .hcTest v (.cp .E)
      (Function.update (Function.update v rT 0) rWp (v rWp + (Nat.bits (v rT)).length)) :=
  halvCount_loop (CA N mode) orc y rT rWp (by decide) .hcTest .hcHalve .hcBump (.cp .E) rfl rfl
    rfl B v hv hc

/-- **The position comparison**: counting `rT` up from `0` reaches the position before
`n + 1` iff the position is at most `n + 1`. -/
theorem le_run (y : List Bool) (B : ℕ) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B) (ht : v rT = 0) :
    Reach N mode y B .leT1 v (if v rPos ≤ v rN1 then .leClr else .rej)
      (Function.update v rT (min (v rPos) (v rN1))) :=
  le_loop (CA N mode) orc y rT rPos rN1 (by decide) (by decide) .leT1 .leT2 .leBump .leClr .rej
    rfl rfl rfl B v hv (by omega) (by omega)

/-! ## The two scans -/

/-- **The validity scan run**: from `rQ1`, `rQ2` at the starts of the words `u`, `u'` read at
stride two and `rE` at the end of `u`, the scan ends in `vDone` of the fold of the letter
step over the zipped words. -/
theorem v_run (y : List Bool) (B : ℕ) (u u' : List Bool) (hlen : u'.length = u.length)
    (st : VAd N) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B) (hlim : v rE = v rQ1 + 2 * u.length)
    (hq : v rQ2 + 2 * u.length ≤ B)
    (ho1 : ∀ i < u.length, y.getD (v rQ1 + 2 * i) false = u.getD i false)
    (ho2 : ∀ i < u.length, y.getD (v rQ2 + 2 * i) false = u'.getD i false) :
    Reach N mode y B (.vTest st) v (.vDone ((List.zip u u').foldl (δV N) st))
      (Function.update (Function.update v rQ1 (v rQ1 + 2 * u.length)) rQ2
        (v rQ2 + 2 * u.length)) :=
  scan_loop (CA N mode) orc y rQ1 rQ2 rE (by decide) (by decide) (by decide) jBit (δV N)
    .vTest .vRd1 .vRd2 (vA1 N) (vA2 N) .vDone 2 (by omega) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun st i hi => by simp only [vA1, dif_pos hi]; rfl)
    (fun st => by simp [vA1]) (fun st i hi => by simp only [vA2, dif_pos hi]; rfl)
    (fun st => by simp [vA2]) B u u' hlen st v hv hlim hq
    (fun i hi => by rw [orc_bit]; exact ho1 i hi) (fun i hi => by rw [orc_bit]; exact ho2 i hi)

/-- **The double sliding scan run**, through `rQ3`, `rQ4` up to `rE`. -/
theorem s_run (y : List Bool) (B : ℕ) (I : SInfo N) (f₀ f₁ : Bool) (u u' : List Bool)
    (hlen : u'.length = u.length) (st : SAd N) (v : Fin 21 → ℕ) (hv : ∀ r, v r ≤ B)
    (hlim : v rE = v rQ3 + 2 * u.length) (hq : v rQ4 + 2 * u.length ≤ B)
    (ho1 : ∀ i < u.length, y.getD (v rQ3 + 2 * i) false = u.getD i false)
    (ho2 : ∀ i < u.length, y.getD (v rQ4 + 2 * i) false = u'.getD i false) :
    Reach N mode y B (.sTest I f₀ f₁ st) v (.sFin I f₀ f₁ ((List.zip u u').foldl (δS N I) st))
      (Function.update (Function.update v rQ3 (v rQ3 + 2 * u.length)) rQ4
        (v rQ4 + 2 * u.length)) :=
  scan_loop (CA N mode) orc y rQ3 rQ4 rE (by decide) (by decide) (by decide) jBit (δS N I)
    (.sTest I f₀ f₁) (.sRd1 I f₀ f₁) (.sRd2 I f₀ f₁) (sA1 N I f₀ f₁) (sA2 N I f₀ f₁)
    (.sFin I f₀ f₁) 2 (by omega) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun st i hi => by simp only [sA1, dif_pos hi]; rfl)
    (fun st => by simp [sA1]) (fun st i hi => by simp only [sA2, dif_pos hi]; rfl)
    (fun st => by simp [sA2]) B u u' hlen st v hv hlim hq
    (fun i hi => by rw [orc_bit]; exact ho1 i hi) (fun i hi => by rw [orc_bit]; exact ho2 i hi)

end Complexity.Codec
