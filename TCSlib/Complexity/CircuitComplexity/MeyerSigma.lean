/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerComplete
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.Uniform

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: the atoms of a verifier input

The bridge between the verifier's atoms (`MeyerVerifier.lean`) and the numeric oracles
of the soundness and completeness arguments: on an in-range verifier input, the atoms
are the numeric valuation `NumVal` of the guessed answers (`atoms_vin`); the input-bit
atom is the input bit (`xbOf_eq`); and the description of a circuit of a family deciding
the tableau language answers every query truthfully (`ansD_family`).

## Main definitions

* `Complexity.Meyer.wordOf` — the width-`W` word of a number (`[]` out of range).
* `Complexity.Meyer.AnsOf` — the numeric oracle of a guessed description.
* `Complexity.Meyer.xbOf` — the input-bit atom.

## Main results

* `Complexity.Meyer.atoms_vin` — atoms of an in-range verifier input.
* `Complexity.Meyer.xbOf_eq` — the `CVAL` index query reads the input bit.
* `Complexity.Meyer.query_mem_CVAL_iff` — a family's circuit decides its language.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing BoolCircuit Complexity.TimeHierarchy Complexity.PolyHierarchy Complexity.KarpLipton

variable (M : FinTM Bool)

/-- **The width-`W` word of a number**, `[]` if the number does not fit. -/
def wordOf (W v : ℕ) : List Bool := if v < 2 ^ W then enumWord W v else []

/-- **The numeric oracle of a guessed description** `D` for input `x` at width `W`. -/
noncomputable def AnsOf (W : ℕ) (x D : List Bool) (sel : Sel M) (t a : ℕ) : Bool :=
  ansD M D sel (wordOf W t) (wordOf W a) x

open Classical in
/-- **The input-bit atom**: the `CVAL` query of the circuit "output input `j`". -/
noncomputable def xbOf (x : List Bool) (j : ℕ) : Bool :=
  decide (pairEncode (idxDesc x.length j) x ∈ CVAL)

/-! ### The input-bit atom -/

/-- The circuit on `n` inputs outputting input `j`. -/
def idxCircuit (n j : ℕ) (hj : j < n) : DAGCircuit n where
  gates := []
  output := j
  args_lt := by simp
  output_lt := by simpa using hj

/-- The description of the "output input `j`" circuit is `idxDesc n j`. -/
theorem idxCircuit_encode (n j : ℕ) (hj : j < n) : (idxCircuit n j hj).encode = idxDesc n j := by
  simp [DAGCircuit.encode, idxCircuit, idxDesc, encodeNat, encodeList]

/-- **The index query reads the input bit.**

**Proof sketch.** The index description is the description of the gate-free circuit with
output `j` (`idxCircuit_encode`); a `CVAL` witness for it has the same description, hence
(`DAGCircuit.eq_of_encode_eq`) no gates and output `j`, so its value is `x[j]`. -/
theorem xbOf_eq (x : List Bool) (j : ℕ) (hj : j < x.length) : xbOf x j = x[j] := by
  have key : pairEncode (idxDesc x.length j) x ∈ CVAL ↔ x[j] = true := by
    constructor
    · rintro ⟨x', C', -, hev, heq⟩
      have h1 := congrArg pairFstD heq
      have h2 := congrArg pairSndD heq
      simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h1 h2
      subst h2
      rw [← idxCircuit_encode _ _ hj] at h1
      obtain ⟨-, hg, ho⟩ := DAGCircuit.eq_of_encode_eq h1.symm
      simp only [DAGCircuit.eval, DAGCircuit.values, idxCircuit] at hev hg ho
      rw [ho] at hev
      simpa [hg, List.getD_eq_getElem?_getD, hj] using hev
    · intro hx
      refine ⟨x, idxCircuit x.length j hj, ⟨fun g hg => by simp [idxCircuit] at hg,
        fun g hg => by simp [idxCircuit] at hg⟩, ?_, ?_⟩
      · simp [DAGCircuit.eval, DAGCircuit.values, idxCircuit, List.getD_eq_getElem?_getD, hj, hx]
      · rw [idxCircuit_encode]
  unfold xbOf
  by_cases hb : x[j] = true
  · rw [hb]; simpa using key.mpr hb
  · rw [Bool.eq_false_iff.mpr hb]
    simpa using fun h => hb (key.mp h)

/-! ### The atoms of an in-range input -/

/-- `wordOf` of an in-range number. -/
theorem wordOf_of_lt {W v : ℕ} (h : v < 2 ^ W) : wordOf W v = enumWord W v := by simp [wordOf, h]

variable {M}

/-- **The atoms of an in-range verifier input** are the numeric valuation of its guessed
answers.

**Proof sketch.** Each time and offset word of width `W` is the word of its value
(`enumWord_ctrVal`); its increment is the word of the successor, or `[]` on overflow
(`incFixed_enumWord`, `incFixed_eq_none_iff`); the padded binary code of the unary offset is
the word of its length (`bits_pad`); the remaining atoms are length tests. -/
theorem atoms_vin (Cw cw : ℕ) (x U tw aw jw pw : List Bool)
    (hn : x.length + 2 < 2 ^ wd Cw cw x.length)
    (hlen : evalAtom Cw cw M .lenAll (vin x U tw aw jw pw) = true) :
    (fun α => evalAtom Cw cw M α (vin x U tw aw jw pw)) =
      NumVal M (AnsOf M (wd Cw cw x.length) x (dropMarker U)) (wd Cw cw x.length) x.length
        (ctrVal tw) (ctrVal aw) jw.length (xbOf x jw.length) := by
  simp only [evalAtom, vt_vin, va_vin, vj_vin, vx_vin, decide_eq_true_eq] at hlen
  obtain ⟨h1, h2, h3, h4⟩ := hlen
  have hbj : bjw (vin x U tw aw jw pw) = enumWord (wd Cw cw x.length) jw.length := by
    simp only [bjw, vj_vin, vp_vin] at h4 ⊢
    have hp : pw.length = wd Cw cw x.length - (Nat.bits jw.length).length := by
      simp at h4; omega
    rw [hp, bits_pad _ jw.length (by omega)]
  have htw : tw = enumWord (wd Cw cw x.length) (ctrVal tw) := by
    rw [← h1]; exact (enumWord_ctrVal tw).symm
  have haw : aw = enumWord (wd Cw cw x.length) (ctrVal aw) := by
    rw [← h2]; exact (enumWord_ctrVal aw).symm
  have hvt : ctrVal tw < 2 ^ wd Cw cw x.length := by have := ctrVal_lt tw; rwa [h1] at this
  have hva : ctrVal aw < 2 ^ wd Cw cw x.length := by have := ctrVal_lt aw; rwa [h2] at this
  -- increments of in-range words
  have hinc : ∀ v, v < 2 ^ wd Cw cw x.length →
      (incFixed (enumWord (wd Cw cw x.length) v)).getD [] = wordOf (wd Cw cw x.length) (v + 1) := by
    intro v hv
    by_cases h : v + 1 < 2 ^ wd Cw cw x.length
    · rw [incFixed_enumWord _ v h, wordOf_of_lt h]; rfl
    · have hv' : v = 2 ^ wd Cw cw x.length - 1 := by omega
      rw [hv', enumWord_ones, (incFixed_eq_none_iff _).mpr (by simp)]
      simp [wordOf, show ¬ (2 ^ wd Cw cw x.length - 1 + 1 < 2 ^ wd Cw cw x.length) by omega]
  have hzero : List.replicate (wd Cw cw x.length) false = enumWord (wd Cw cw x.length) 0 :=
    (enumWord_zero _).symm
  have hones : List.replicate (wd Cw cw x.length) true =
      enumWord (wd Cw cw x.length) (2 ^ wd Cw cw x.length - 1) := (enumWord_ones _).symm
  have hpos : 0 < 2 ^ wd Cw cw x.length := Nat.two_pow_pos _
  have hW1 : wd Cw cw x.length ≠ 0 := fun h => by rw [h] at hn; simp at hn
  have htwd : ∀ T, twd Cw cw T (vin x U tw aw jw pw) =
      wordOf (wd Cw cw x.length) (tvOf (wd Cw cw x.length) (ctrVal tw) T) := by
    intro T
    cases T with
    | tc => simp only [twd, vt_vin, tvOf]; rw [wordOf_of_lt hvt]; exact htw
    | tn => simp only [twd, vt_vin, tvOf]; rw [htw, hinc _ hvt, ← htw]
    | t0 => simp only [twd, vx_vin, tvOf]; rw [wordOf_of_lt hpos]; exact hzero
    | t1 => simp only [twd, vx_vin, tvOf]; rw [wordOf_of_lt (by omega)]; exact hones
  have hawd : ∀ A, awd Cw cw A (vin x U tw aw jw pw) =
      wordOf (wd Cw cw x.length) (avOf (ctrVal aw) jw.length A) := by
    intro A
    cases A with
    | ac => simp only [awd, va_vin, avOf]; rw [wordOf_of_lt hva]; exact haw
    | an => simp only [awd, va_vin, avOf]; rw [haw, hinc _ hva, ← haw]
    | a0 => simp only [awd, vx_vin, avOf]; rw [wordOf_of_lt hpos]; exact hzero
    | a1 => simp only [awd, vx_vin, avOf]; rw [hzero, hinc 0 hpos]
    | aj => simp only [awd, avOf]; rw [hbj, wordOf_of_lt (by omega)]
    | aj1 => simp only [awd, avOf]; rw [hbj, hinc _ (by omega)]
  funext α
  cases α with
  | ans sel T A => simp only [evalAtom, NumVal, AnsOf, vD_vin, vx_vin, htwd, hawd]
  | lenAll =>
    simp only [evalAtom, NumVal, vt_vin, va_vin, vj_vin, vx_vin, decide_eq_true_eq]
    exact ⟨h1, h2, h3, h4⟩
  | tNotOnes =>
    simp only [evalAtom, NumVal, vt_vin]
    rw [htw, hinc _ hvt, ← htw]
    by_cases h : ctrVal tw + 1 < 2 ^ wd Cw cw x.length
    · rw [wordOf_of_lt h]
      have : enumWord (wd Cw cw x.length) (ctrVal tw + 1) ≠ [] := by
        intro h0; have := congrArg List.length h0; simp at this; omega
      simp [h, this]
    · simp [h, wordOf]
  | aNotOnes =>
    simp only [evalAtom, NumVal, va_vin]
    rw [haw, hinc _ hva, ← haw]
    by_cases h : ctrVal aw + 1 < 2 ^ wd Cw cw x.length
    · rw [wordOf_of_lt h]
      have : enumWord (wd Cw cw x.length) (ctrVal aw + 1) ≠ [] := by
        intro h0; have := congrArg List.length h0; simp at this; omega
      simp [h, this]
    · simp [h, wordOf]
  | aZero =>
    simp only [evalAtom, NumVal, va_vin]
    congr 1
    apply propext
    constructor
    · intro h
      have := congrArg ctrVal h
      rw [h2, hzero, ctrVal_enumWord _ 0 hpos] at this
      exact this
    · intro h
      rw [h2, haw, h, enumWord_zero]
  | jZero => simp [evalAtom, NumVal]
  | jLtN => simp [evalAtom, NumVal]
  | jLeN => simp [evalAtom, NumVal]
  | jEqN1 => simp [evalAtom, NumVal]
  | xbit => simp [evalAtom, NumVal, xbOf]

/-! ### Circuits of a family -/

/-- **A family's circuit decides the family's language** through `CVAL`: for a fan-in-two
family, the description of the circuit for length `|q|` accepts `q` iff `q` is in the
family's language. -/
theorem query_mem_CVAL_iff {F : DAGCircuitFamily} (hF : F.HasFaninTwo) (q : List Bool) :
    pairEncode (F.circuit q.length).encode q ∈ CVAL ↔ q ∈ F.language := by
  constructor
  · rintro ⟨x', C', -, hev, heq⟩
    obtain ⟨h1, h2⟩ := Prod.mk.inj (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) heq)
    subst h2
    have h3 := DAGCircuit.encode_injective _ h1
    rw [F.mem_language_iff, h3]
    exact hev
  · intro hmem
    exact ⟨q, F.circuit q.length, hF _, hmem, rfl⟩

/-- **The numeric oracle of a family's description is truthful**: if `F` decides the
tableau language of `M` and `D` is the description of its circuit for the query length
`nbits + 4W + 4 + |x|`, every in-range query is answered with the true tableau bit. -/
theorem ansD_family {F : DAGCircuitFamily} (hF : F.HasFaninTwo) (hFL : F.language = Tab M)
    (W : ℕ) (x : List Bool) (sel : Sel M) (t a : ℕ) (ht : t < 2 ^ W) (ha : a < 2 ^ W) :
    AnsOf M W x (F.circuit (nbits M + 2 * W + 2 * W + 4 + x.length)).encode sel t a =
      tabAns M sel (M.tm.runFrom (M.tm.initCfg x) t) a := by
  have hq : tabFun M (query (encodeSel sel) (enumWord W t) (enumWord W a) x) =
      tabAns M sel (M.tm.runFrom (M.tm.initCfg x) t) a := by
    rw [tabFun_query, ctrVal_enumWord W t ht, ctrVal_enumWord W a ha]
  have hlen : (query (encodeSel sel) (enumWord W t) (enumWord W a) x).length =
      nbits M + 2 * W + 2 * W + 4 + x.length := by simp
  rw [← hq]
  unfold AnsOf ansD
  rw [wordOf_of_lt ht, wordOf_of_lt ha, ← hlen]
  have := query_mem_CVAL_iff hF (query (encodeSel sel) (enumWord W t) (enumWord W a) x)
  rw [hFL] at this
  by_cases hb : tabFun M (query (encodeSel sel) (enumWord W t) (enumWord W a) x) = true
  · rw [hb]; simpa using this.mpr hb
  · rw [Bool.eq_false_iff.mpr hb]; simpa using fun h => hb (this.mp h)

end Complexity.Meyer
