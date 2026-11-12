/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.Randomized.ZeroP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial identity testing is in coRP

[AB09, §7.2.3, p.129] reduces deciding "do the circuits `C` and `C′` compute the same
polynomial?" to `ZEROP` through the circuit `D = C − C′`. Here that language, `PITLang`, gets
the verifier which runs the ZEROP test of [AB09, §7.2.3, p.130] on `D`
(`Randomized.AlgCircuit.subCircuit`), so `PITLang ∈ coRP` and `PITLang ∈ BPP`, in the
certificate form over `Randomized.polyTimeModel` and in the PTM form.

## Main definitions

* `Randomized.PITLang` — pairs `⟨C, C′⟩` of well-formed `n`-variable circuits with
  `C ≡ C′` as polynomials.
* `Randomized.pitVerifier` — the ZEROP test on `C − C′`; `Randomized.PIT.pitW` on words.

## Main results

* `Randomized.pitVerifier_spec` — one-sided error `≤ 1/3`.
* `Randomized.eff_pitVerifier` — the verifier is polynomial-time.
* `Randomized.inCoRP_PITLang`, `Randomized.inBPP_PITLang`, `Randomized.PITLang_mem_coRP_PTM`,
  `Randomized.PITLang_mem_BPP_PTM`.

## Divergences

* The book states the reduction to `ZEROP` and leaves the rest implicit; here identity
  testing gets its own verifier (the ZEROP test on `C − C′`, with `C(a) − C′(a) ≡ 0 (mod k)`
  computed as the comparison of the two residues). The polynomial-time map
  `⟨C, C′⟩ ↦ code(C − C′)` is `Randomized.PITLang_le_ZEROP`
  (`TCSlib.Complexity.Randomized.ZeroPReduce`). `PITLang` asks both circuits to be well
  formed over the same number of variables; malformed pairs are outside it.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized

open Complexity Turing AlgCircuit PIT BinArith
open Complexity.LogProg (bitsVal bitsVal_bits)

/-- **Polynomial identity testing** [AB09, §7.2.3, p.129]: the pairs `⟨C, C′⟩` (of codes) of
well-formed `n`-variable algebraic circuits computing the same polynomial. -/
def PITLang : Language Bool :=
  {x | ∃ (n : ℕ) (C C' : AlgCircuit n),
    pairEncode (AlgCircuit.encode ⟨n, C⟩) (AlgCircuit.encode ⟨n, C'⟩) = x ∧
      C.WellFormed ∧ C'.WellFormed ∧ C.toMvPolynomial = C'.toMvPolynomial}

/-- The verifier for the complement of `PITLang`: decode `⟨C, C′⟩`; output `true` ("not in
PIT") if this fails, and otherwise iff the ZEROP test rejects `C − C′`. -/
def pitVerifier (x r : List Bool) : Bool :=
  match AlgCircuit.decode (pairFstD x), AlgCircuit.decode (pairSndD x) with
  | some ⟨n, C⟩, some ⟨n', C'⟩ =>
    if h : n' = n then
      (if C.WellFormed ∧ C'.WellFormed then !((C.subCircuit (h ▸ C')).zeroTest r) else true)
    else true
  | _, _ => true

/-- The verifier on a decoded pair over the same number of variables. -/
theorem pitVerifier_of_decode {x : List Bool} {n : ℕ} {C C' : AlgCircuit n}
    (h₁ : AlgCircuit.decode (pairFstD x) = some ⟨n, C⟩)
    (h₂ : AlgCircuit.decode (pairSndD x) = some ⟨n, C'⟩) (r : List Bool) :
    pitVerifier x r =
      if C.WellFormed ∧ C'.WellFormed then !((C.subCircuit C').zeroTest r) else true := by
  simp only [pitVerifier, h₁, h₂, dite_true]

/-- Off decoded well-formed pairs the verifier answers `true`. -/
theorem pitVerifier_of_not {x : List Bool}
    (hg : ¬ ∃ (n : ℕ) (C C' : AlgCircuit n), AlgCircuit.decode (pairFstD x) = some ⟨n, C⟩ ∧
      AlgCircuit.decode (pairSndD x) = some ⟨n, C'⟩ ∧ C.WellFormed ∧ C'.WellFormed)
    (r : List Bool) : pitVerifier x r = true := by
  unfold pitVerifier
  rcases h₁ : AlgCircuit.decode (pairFstD x) with _ | ⟨n, C⟩ <;>
    rcases h₂ : AlgCircuit.decode (pairSndD x) with _ | ⟨n', C'⟩
  · rfl
  · rfl
  · rfl
  · dsimp only
    split_ifs with h hw
    · subst h
      exact absurd ⟨n', C, C', h₁, h₂, hw.1, hw.2⟩ hg
    · rfl
    · rfl

/-- A word whose first component decodes is a pair. -/
theorem eq_pairEncode_of_decode {x : List Bool} {c : (n : ℕ) × AlgCircuit n}
    (h : AlgCircuit.decode (pairFstD x) = some c) :
    x = pairEncode (pairFstD x) (pairSndD x) := by
  cases hd : pairDecode x with
  | none =>
    have h0 : pairFstD x = [] := by simp [pairFstD, hd]
    rw [h0] at h
    cases h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hx := eq_pairEncode_of_pairDecode x a b hd
    rw [hx]
    simp

/-- Membership in `PITLang` through the decoder. -/
theorem mem_PITLang_iff (x : List Bool) :
    x ∈ PITLang ↔ ∃ (n : ℕ) (C C' : AlgCircuit n),
      AlgCircuit.decode (pairFstD x) = some ⟨n, C⟩ ∧
        AlgCircuit.decode (pairSndD x) = some ⟨n, C'⟩ ∧ C.WellFormed ∧ C'.WellFormed ∧
          C.toMvPolynomial = C'.toMvPolynomial := by
  constructor
  · rintro ⟨n, C, C', rfl, hw, hw', hp⟩
    exact ⟨n, C, C', by simp [decode_encode], by simp [decode_encode], hw, hw', hp⟩
  · rintro ⟨n, C, C', h₁, h₂, hw, hw', hp⟩
    refine ⟨n, C, C', ?_, hw, hw', hp⟩
    rw [encode_of_decode h₁, encode_of_decode h₂]
    exact (eq_pairEncode_of_decode h₁).symm

/-- **The one-sided error of identity testing** [AB09, §7.2.3]: pairs outside `PITLang` are
certified with probability `≥ 2/3`, pairs in it never are.

**Proof sketch.** Off decoded well-formed pairs the verifier always certifies. On a decoded
well-formed pair, `D = C − C′` is well formed and computes `C − C′`, which is nonzero iff
`C ≢ C′` (`toMvPolynomial_eq_iff_subCircuit`); the soundness and completeness of the ZEROP test
on `D` give the two clauses, and `|D| + n ≤ |x|` bounds its coins. -/
theorem pitVerifier_spec (x : List Bool) :
    (x ∉ PITLang → 2 / 3 ≤ randProb (polyLen 2400 2 x.length)
      (fun r => pitVerifier x r = true)) ∧
    (x ∈ PITLang → ∀ r : Fin (polyLen 2400 2 x.length) → Bool,
      pitVerifier x (List.ofFn r) = false) := by
  constructor
  · intro hx
    by_cases hg : ∃ (n : ℕ) (C C' : AlgCircuit n), AlgCircuit.decode (pairFstD x) = some ⟨n, C⟩ ∧
        AlgCircuit.decode (pairSndD x) = some ⟨n, C'⟩ ∧ C.WellFormed ∧ C'.WellFormed
    · obtain ⟨n, C, C', h₁, h₂, hw, hw'⟩ := hg
      have hz : (C.subCircuit C').toMvPolynomial ≠ 0 := fun hz =>
        hx ((mem_PITLang_iff x).2 ⟨n, C, C', h₁, h₂, hw, hw',
          (toMvPolynomial_eq_iff_subCircuit hw.1 hw'.1).2 hz⟩)
      have hlen : testLen n (C.subCircuit C').size ≤ polyLen 2400 2 x.length := by
        have e₁ := lt_length_encode ⟨n, C⟩
        have e₂ := lt_length_encode ⟨n, C'⟩
        rw [encode_of_decode h₁] at e₁
        rw [encode_of_decode h₂] at e₂
        have hx' : x.length = 2 * (pairFstD x).length + 2 + (pairSndD x).length := by
          conv_lhs => rw [eq_pairEncode_of_decode h₁]
          exact length_pairEncode _ _
        simp only at e₁ e₂
        rw [size_subCircuit]
        exact testLen_le_polyLen_of_le (by omega) (by omega)
      rw [randProb_congr (B := fun r => (C.subCircuit C').zeroTest r = false) fun r => by
        rw [pitVerifier_of_decode h₁ h₂, if_pos ⟨hw, hw'⟩]
        dsimp only
        generalize (C.subCircuit C').zeroTest (List.ofFn r) = t
        cases t <;> decide]
      exact zeroTest_sound _ hz hlen
    · rw [randProb_congr (B := fun _ => True) fun r =>
        iff_of_true (pitVerifier_of_not hg _) trivial, randProb_true]
      norm_num
  · intro hx r
    obtain ⟨n, C, C', h₁, h₂, hw, hw', hp⟩ := (mem_PITLang_iff x).1 hx
    rw [pitVerifier_of_decode h₁ h₂, if_pos ⟨hw, hw'⟩,
      zeroTest_of_toMvPolynomial_eq_zero ((toMvPolynomial_eq_iff_subCircuit hw.1 hw'.1).1 hp)]
    rfl

namespace PIT

/-- **The identity-testing verifier on words**: on `⟨⟨x₁, x₂⟩, r⟩` with `x₁, x₂` codes of
well-formed circuits over the same inputs, run the pipeline on the two codes with size
`|C| + |C′| + 1` (that of `C − C′`), and negate; otherwise `true`. -/
def pitW (z : List Bool) : Bool :=
  !(validW (pairFstD (pairFstD z)) && validW (pairSndD (pairFstD z)) &&
      decide ((uHead (pairFstD (pairFstD z))).length = (uHead (pairSndD (pairFstD z))).length)) ||
    !pipe (pairEncode (uHead (pairFstD (pairFstD z)))
      (pairEncode (sI (scanRun (pairFstD (pairFstD z))) ++ sI (scanRun (pairSndD (pairFstD z))) ++
          [true])
        (pairEncode (uRest (pairFstD (pairFstD z)))
          (pairEncode (uRest (pairSndD (pairFstD z))) (pairSndD z)))))

/-- The identity-testing verifier on words is polynomial-time.

**Proof sketch.** The validity tests (`polyTimeComputable_validW`), the unary-prefix
comparison (`uHead`, `polyTimeComputable_lenEq`) and the packing of the pipeline's input
(`uHead`, `uRest`, the circuit-size scans) compose from the kit; the verifier is a Boolean
combination of these and of `polyTimeComputable_pipe`. -/
theorem polyTimeComputable_pitW : PolyTimeComputable (fun z => [pitW z]) := by
  have h₁ : PolyTimeComputable (fun z => pairFstD (pairFstD z)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have h₂ : PolyTimeComputable (fun z => pairSndD (pairFstD z)) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hsI : PolyTimeComputable (fun x => sI (scanRun x)) :=
    @polyTimeComputable_app sI scanRun
      (polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3)
      polyTimeComputable_scanRun
  have hv₁ := polyTimeComputable_test_app polyTimeComputable_validW h₁
  have hv₂ := polyTimeComputable_test_app polyTimeComputable_validW h₂
  have hu₁ := polyTimeComputable_app polyTimeComputable_uHead h₁
  have hu₂ := polyTimeComputable_app polyTimeComputable_uHead h₂
  have heq : PolyTimeComputable (fun z => [decide ((uHead (pairFstD (pairFstD z))).length =
      (uHead (pairSndD (pairFstD z))).length)]) := by
    have := polyTimeComputable_test_app polyTimeComputable_lenEq (hu₁.pairEncode hu₂)
    simpa only [pairFstD_pairEncode, pairSndD_pairEncode] using this
  have hpack : PolyTimeComputable (fun z => pairEncode (uHead (pairFstD (pairFstD z)))
      (pairEncode (sI (scanRun (pairFstD (pairFstD z))) ++ sI (scanRun (pairSndD (pairFstD z))) ++
          [true])
        (pairEncode (uRest (pairFstD (pairFstD z)))
          (pairEncode (uRest (pairSndD (pairFstD z))) (pairSndD z))))) :=
    hu₁.pairEncode ((((polyTimeComputable_app hsI h₁).append (polyTimeComputable_app hsI h₂)).append
      (polyTimeComputable_const [true])).pairEncode
      ((polyTimeComputable_app polyTimeComputable_uRest h₁).pairEncode
        ((polyTimeComputable_app polyTimeComputable_uRest h₂).pairEncode
          polyTimeComputable_pairSndD)))
  exact polyTimeComputable_or
    (polyTimeComputable_not (polyTimeComputable_and (polyTimeComputable_and hv₁ hv₂) heq))
    (polyTimeComputable_not (polyTimeComputable_test_app polyTimeComputable_pipe hpack))

/-- **The word-level verifier computes `pitVerifier`.**

**Proof sketch.** On a decoded well-formed pair over `n` inputs the codes are `1ⁿ0·code(C)`
and `1ⁿ0·code(C′)`, the scans count `|C|` and `|C′|`, and `pipe_eq` turns the pipeline into
"equal residues modulo every modulus"; by `evalModW_spec` the residues are those of `C(a)`
and `C′(a)`, and `C(a) ≡ C′(a)` iff `(C − C′)(a) ≡ 0` (`eval_subCircuit`), which is the ZEROP
test on `C − C′` (`zeroTest_eq`). Otherwise both sides are `true`. -/
theorem pitW_pairEncode (x r : List Bool) : pitW (pairEncode x r) = pitVerifier x r := by
  simp only [pitW, pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases hg : (validW (pairFstD x) && validW (pairSndD x) &&
      decide ((uHead (pairFstD x)).length = (uHead (pairSndD x)).length)) = true
  · rw [hg, Bool.not_true, Bool.false_or]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    obtain ⟨⟨hv₁, hv₂⟩, hn⟩ := hg
    obtain ⟨⟨n, C⟩, hd₁, hw⟩ := (validW_iff _).mp hv₁
    obtain ⟨⟨n', C'⟩, hd₂, hw'⟩ := (validW_iff _).mp hv₂
    have hx₁ := encode_of_decode hd₁
    have hx₂ := encode_of_decode hd₂
    simp only [encode] at hx₁ hx₂
    have hu₁ : uHead (pairFstD x) = List.replicate n true := by rw [← hx₁, uHead_encodeNat]
    have hu₂ : uHead (pairSndD x) = List.replicate n' true := by rw [← hx₂, uHead_encodeNat]
    rw [hu₁, hu₂, List.length_replicate, List.length_replicate] at hn
    subst hn
    have hr₁ : uRest (pairFstD x) = encodeGates C.gates := by rw [← hx₁, uRest_encodeNat]
    have hr₂ : uRest (pairSndD x) = encodeGates C'.gates := by rw [← hx₂, uRest_encodeNat]
    have hI : sI (scanRun (pairFstD x)) ++ sI (scanRun (pairSndD x)) ++ [true] =
        List.replicate (C.subCircuit C').size true := by
      rw [sI_scanRun hd₁ hw, sI_scanRun hd₂ hw', size_subCircuit, List.replicate_add,
        List.replicate_add]
      rfl
    rw [hu₁, hI, hr₁, hr₂, pipe_eq, pitVerifier_of_decode hd₁ hd₂, if_pos ⟨hw, hw'⟩,
      zeroTest_eq]
    refine congrArg (fun b => !b) ?_
    rw [decide_eq_decide]
    refine forall_congr' fun j => imp_congr_right fun _ => ?_
    obtain ⟨hlt₁, hc₁⟩ := evalModW_spec (rawj n (C.subCircuit C').size r j)
      (pts n (C.subCircuit C').size r) C hw
    obtain ⟨hlt₂, hc₂⟩ := evalModW_spec (rawj n (C.subCircuit C').size r j)
      (pts n (C.subCircuit C').size r) C' hw'
    rw [eval_subCircuit hw.1 hw'.1, sub_eq_zero, ← hc₁, ← hc₂, ZMod.natCast_eq_natCast_iff',
      Nat.mod_eq_of_lt hlt₁, Nat.mod_eq_of_lt hlt₂]
  · rw [Bool.eq_false_iff.mpr hg, Bool.not_false, Bool.true_or]
    refine (pitVerifier_of_not (fun h => hg ?_) r).symm
    obtain ⟨n, C, C', h₁, h₂, hw, hw'⟩ := h
    have hx₁ := encode_of_decode h₁
    have hx₂ := encode_of_decode h₂
    simp only [encode] at hx₁ hx₂
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨(validW_iff _).mpr ⟨_, h₁, hw⟩, (validW_iff _).mpr ⟨_, h₂, hw'⟩⟩, ?_⟩
    rw [← hx₁, ← hx₂, uHead_encodeNat, uHead_encodeNat]

end PIT

/-- **The identity-testing verifier is polynomial-time.** [AB09, §7.2.3] -/
theorem eff_pitVerifier : polyTimeModel.Eff (boolVerifier pitVerifier) :=
  eff_boolVerifier_of_test PIT.polyTimeComputable_pitW PIT.pitW_pairEncode

/-- **Polynomial identity testing is in `coRP`** [AB09, §7.2.3], certificate form. -/
theorem inCoRP_PITLang : InCoRP polyTimeModel PITLang :=
  ⟨pitVerifier, 2400, 2, eff_pitVerifier, fun x =>
    ⟨fun hx => (pitVerifier_spec x).1 hx,
      fun hx => (pitVerifier_spec x).2 (by by_contra h; exact hx h)⟩⟩

/-- **Polynomial identity testing is in `BPP`**, certificate form [AB09, §7.2.3]. -/
theorem inBPP_PITLang : InBPP polyTimeModel PITLang :=
  InCoRP.inBPP_polyTime inCoRP_PITLang

/-- **Polynomial identity testing is in `coRP`**, PTM form [AB09, Def 7.6]. -/
theorem PITLang_mem_coRP_PTM : PITLang ∈ coRP_PTM :=
  (mem_coRP_PTM_iff _).2 inCoRP_PITLang

/-- **Polynomial identity testing is in `BPP`**, PTM form [AB09, Def 7.2]. -/
theorem PITLang_mem_BPP_PTM : PITLang ∈ BPP_PTM :=
  (mem_BPP_PTM_iff _).2 inBPP_PITLang

end Randomized
