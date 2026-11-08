/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Infrastructure for the hardness of the universal one-way function

Generic lemmas used by the proof of [PS10, Theorem 63.1] in
`TCSlib.Cryptography.Asymptotic.Universal` (`fUniversal_hard`): the closure lemma
`Complexity.NUPPT.exists_reparam_pre_post` (a parameter change `m ↦ φ m` together with an
advice-dependent polynomial-time pre-processing and a polynomial-time post-processing — the
shape of the reduction "`B(1^m, y)` runs `A(1^n, ⟨M_g, y⟩ padded)` and strips the code field"),
the arithmetic fact `2 ⌊log₂ n⌋ ≤ n` behind the majorant `n ≤ 2(n − ⌊log₂ n⌋)` of the
reparametrisation, and two list facts: zero-padded pairs with first components of equal length
agree on their first components (the step "an answer `⟨M', x'⟩` with equal padded output has
`M' = M_g`"), and a string of length `m` is the encoding of some `m`-bit string.

## Main definitions

None: this file is proof infrastructure for `TCSlib.Cryptography.Asymptotic.Universal`.

## Main results

* `Complexity.NUPPT.exists_reparam_pre_post`, `Complexity.NUPPT.exists_reparam_pre_post_adv` —
  reparametrisation with pre- and post-processing (the latter with the advice visible to the
  post-processing).
* `TCSlib.Cryptography.length_tail_bits`, `TCSlib.Cryptography.polyTimeComputable_logMarker`,
  `TCSlib.Cryptography.polyTimeComputable_univBudget` — the split marker `(bits |y|).tail` of
  `⌊log₂ |y|⌋` bits and the binary budget `bits ((|y| + 1)³)` are polynomial-time.
* `TCSlib.Cryptography.length_serialize_decode_le`,
  `TCSlib.Cryptography.numStates_add_one_le_length_serialize` (with `length_signBits`,
  `two_le_length_actionBits`, `length_le_length_flatMap`) — the serialization of a decoded
  code is bounded by the canonizer's time and bounds the number of states (used by
  `exists_univCoeff_le`).
* `TCSlib.Cryptography.two_mul_log_two_le` — `2 ⌊log₂ n⌋ ≤ n`;
  `TCSlib.Cryptography.quadratic_le_cubic` — `c₀ (m + 1)² ≤ (n + 1)³` for `m ≤ n`, `c₀ ≤ n + 1`.
* `TCSlib.Cryptography.pairEncode_append_eq` — zero-padded pairs with equal-length first
  components agree on the first component and on the padded second components.
* `TCSlib.Cryptography.exists_ofFn_eq_of_length`, `TCSlib.Cryptography.take_append_replicate_of_le`
  — encoding and padding facts.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13, Theorem 63.1.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-- Composition of polynomial-time functions, in applied form (private copy of the helper
of `TCSlib.Complexity.Randomized.Closure`). -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-! ## The closure lemma -/

/-- **Parameter change with advice-dependent pre-processing and post-processing**
[PS10, §2.1, implicit; the reduction of Theorem 63.1]: for an `NUPPT` `A`, a map `φ : ℕ → ℕ`
majorised by the syntactic polynomial `p`, an advice family `β m` of length `≤ b m`, and
polynomial-time `pre`, `post`, there is an `NUPPT` `B` with coins `A.coins.subst p` such that
`B(1^m, y; r) = post (A(1^{φ m}, pre ⟨β m, y⟩; r.take (A.coins (φ m))))` — extra coins are unread.

**Proof sketch.** Advice `⟨⟨1^{φ m}, A.advice (φ m)⟩, β m⟩`, of length
`≤ 4 p(m) + 6 + 2 A.adv(p(m)) + b(m)` (`length_pairEncode`, `hφ`, `advice_length`,
`PolyExpr.eval_mono`). The raw function reads `w := 1^{φ m}`, `α := A.advice (φ m)` and `β m`
from the advice slot, pairs `β m` with the argument slot and applies `pre`, cuts the coins to
`A.coins.eval |w|` bits (`polyTimeComputable_pairTakePoly A.coins` on `⟨w, inCoins z⟩`), runs
`A.output` on `layout w (pre ⟨β m, y⟩) α coins'` and applies `post`; the equation is
`NUPPT.runAtL_ofPolyTime` plus the projection identities of the layout. -/
theorem _root_.Complexity.NUPPT.exists_reparam_pre_post (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ m, φ m ≤ p.eval m) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ m, (β m).length ≤ b.eval m) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ ∀ m y r, B.runAtL m y r =
      post (A.runAtL (φ m) (pre (pairEncode (β m) y)) (r.take (A.coinLen (φ m)))) := by
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairFstD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hαA : PolyTimeComputable fun z => pairSndD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairSndD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hβm : PolyTimeComputable fun z => pairSndD (NUPPT.inAdvice z) :=
    ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice
  have hF := ptc_comp hpost (ptc_comp A.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout hw
      (ptc_comp hpre (hβm.pairEncode NUPPT.polyTimeComputable_inArg)) hαA
      (ptc_comp (polyTimeComputable_pairTakePoly A.coins)
        (hw.pairEncode NUPPT.polyTimeComputable_inCoins))))
  have hadv : ∀ m, (pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m)))
      (β m)).length ≤
      (PolyExpr.add (.add (.add (.mul (.const 4) p) (.const 6)) (.mul (.const 2) (A.adv.subst p)))
        b).eval m := by
    intro m
    simp only [length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ m
    have h₂ := A.advice_length (φ m)
    have h₃ := A.adv.eval_mono (hφ m)
    have h₄ := hβ m
    omega
  refine ⟨NUPPT.ofPolyTime hF (A.coins.subst p) _
    (fun m => pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m))) (β m)) hadv,
    rfl, fun m y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.advInput, NUPPT.coinLen, NUPPT.layout, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins]

/-- **Parameter change with advice-dependent pre- and post-processing**: as
`exists_reparam_pre_post`, but the post-processing also reads the advice: `B(1^m, y; r) =
post ⟨β m, A(1^{φ m}, pre ⟨β m, y⟩; r.take (A.coins (φ m)))⟩` (the reduction of
[PS10, Lemma 64.3] cuts `A`'s answer to a length stored in the advice).

**Proof sketch.** As `exists_reparam_pre_post`, with the raw function
`post ⟨β m, A.output (layout w (pre ⟨β m, y⟩) α coins')⟩`. -/
theorem _root_.Complexity.NUPPT.exists_reparam_pre_post_adv (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ m, φ m ≤ p.eval m) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ m, (β m).length ≤ b.eval m) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ ∀ m y r, B.runAtL m y r =
      post (pairEncode (β m)
        (A.runAtL (φ m) (pre (pairEncode (β m) y)) (r.take (A.coinLen (φ m))))) := by
  have hw : PolyTimeComputable fun z => pairFstD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairFstD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hαA : PolyTimeComputable fun z => pairSndD (pairFstD (NUPPT.inAdvice z)) :=
    ptc_comp polyTimeComputable_pairSndD
      (ptc_comp polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inAdvice)
  have hβm : PolyTimeComputable fun z => pairSndD (NUPPT.inAdvice z) :=
    ptc_comp polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inAdvice
  have hF := ptc_comp hpost (hβm.pairEncode (ptc_comp A.polyTimeComputable_output
    (NUPPT.polyTimeComputable_layout hw
      (ptc_comp hpre (hβm.pairEncode NUPPT.polyTimeComputable_inArg)) hαA
      (ptc_comp (polyTimeComputable_pairTakePoly A.coins)
        (hw.pairEncode NUPPT.polyTimeComputable_inCoins)))))
  have hadv : ∀ m, (pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m)))
      (β m)).length ≤
      (PolyExpr.add (.add (.add (.mul (.const 4) p) (.const 6)) (.mul (.const 2) (A.adv.subst p)))
        b).eval m := by
    intro m
    simp only [length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ m
    have h₂ := A.advice_length (φ m)
    have h₃ := A.adv.eval_mono (hφ m)
    have h₄ := hβ m
    omega
  refine ⟨NUPPT.ofPolyTime hF (A.coins.subst p) _
    (fun m => pairEncode (pairEncode (List.replicate (φ m) true) (A.advice (φ m))) (β m)) hadv,
    rfl, fun m y r => ?_⟩
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAtL, NUPPT.advInput, NUPPT.coinLen, NUPPT.layout, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins]

/-! ## The split marker and the budget of Algorithm 64.2 -/

/-- The tail of the binary representation of `m` has `⌊log₂ m⌋` bits: `Nat.bits 0 = []`
and `Nat.size m = ⌊log₂ m⌋ + 1` for `m ≥ 1` (`Nat.lt_size`, `Nat.size_le`). -/
theorem length_tail_bits (m : ℕ) : (Nat.bits m).tail.length = Nat.log 2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [List.length_tail, Nat.size_eq_bits_len]
    have h1 : Nat.log 2 m < Nat.size m := Nat.lt_size.mpr (Nat.pow_log_le_self 2 hm.ne')
    have h2 : Nat.size m ≤ Nat.log 2 m + 1 :=
      Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) m)
    omega

/-- The marker `(bits |y|).tail`, a string of `⌊log₂ |y|⌋` bits, is polynomial-time in `y`
(`Turing.FinTM.computesFunInTime_lengthBits`, `Complexity.StateLoop.tail_poly`). -/
theorem polyTimeComputable_logMarker :
    PolyTimeComputable fun y : List Bool => (Nat.bits y.length).tail :=
  StateLoop.tail_poly.comp (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits)

/-- The binary budget `bits ((|y| + 1)³)` of [PS10, Algorithm 64.2] is polynomial-time
(`Turing.FinTM.computesFunInTime_polyBits 1 3`). -/
theorem polyTimeComputable_univBudget :
    PolyTimeComputable fun y : List Bool => Nat.bits ((y.length + 1) ^ 3) := by
  obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_polyBits 1 3
  refine ⟨M, a, 4, fun y => ?_⟩
  simpa using hM y

/-! ## Serialization lengths of coded machines -/

/-- The serialization of a decoded code is no longer than the canonizer's running time on the
code (output length is at most the number of steps). -/
theorem length_serialize_decode_le (c : EffectiveMachineCode) (α : List Bool) :
    (c.decode α).serialize.length ≤ c.canonizerTime α.length := by
  have h := c.canonizer_computes α
  obtain ⟨-, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  have ho' : (c.canonizer.tm.runFrom (c.canonizer.tm.initCfg α) (c.canonizerTime α.length)).output =
      (c.decode α).serialize := ho
  rw [← ho']
  exact c.canonizer.tm.output_length_le α _

/-- The sign serialization has two bits. -/
theorem length_signBits (s : SignType) : (signBits s).length = 2 := by cases s <;> rfl

/-- The serialization of a transition record has at least two bits (its sign field). -/
theorem two_le_length_actionBits {n : ℕ} (a : Action 1 Bool (Fin (n + 1))) :
    2 ≤ (actionBits a).length := by
  simp only [actionBits, List.length_append, length_signBits]
  omega

/-- A `flatMap` whose pieces are all nonempty is at least as long as the index list. -/
theorem length_le_length_flatMap {α : Type*} (l : List α) (f : α → List Bool)
    (hf : ∀ a, 1 ≤ (f a).length) : l.length ≤ (l.flatMap f).length := by
  rw [List.length_flatMap]
  refine le_trans (by simp) (List.length_le_sum_of_one_le _ fun x hx => ?_)
  obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
  exact hf a

/-- The serialization of a coded machine lists one nonempty transition block per state, so it
has at least `numStates + 1` bits (`Turing.CodeTM.serialize`). -/
theorem numStates_add_one_le_length_serialize (M : CodeTM) :
    M.numStates + 1 ≤ M.serialize.length := by
  have h1 : ∀ q : Fin (M.numStates + 1), 1 ≤
      (([none, some false, some true] : List (Option Bool)).flatMap fun inp =>
        ([none, some false, some true] : List (Option Bool)).flatMap fun w =>
          actionBits (M.tm.tr q inp fun _ => w)).length := by
    intro q
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append]
    have := two_le_length_actionBits (M.tm.tr q none fun _ => none)
    omega
  have h2 := length_le_length_flatMap (List.finRange (M.numStates + 1)) _ h1
  rw [List.length_finRange] at h2
  rw [CodeTM.serialize, length_pairEncode, List.length_append]
  omega

/-! ## Arithmetic and list facts -/

/-- The budget of `f_universal` covers a quadratic machine on the argument field:
`c₀ (m + 1)² ≤ (n + 1)³` for `m ≤ n` and `c₀ ≤ n + 1`. -/
theorem quadratic_le_cubic {c₀ m n : ℕ} (hm : m ≤ n) (hc : c₀ ≤ n + 1) :
    c₀ * (m + 1) ^ 2 ≤ (n + 1) ^ 3 := by
  calc c₀ * (m + 1) ^ 2 ≤ (n + 1) * (n + 1) ^ 2 :=
        Nat.mul_le_mul hc (Nat.pow_le_pow_left (by omega) 2)
    _ = (n + 1) ^ 3 := by ring

/-- `2k ≤ 2^k` for every `k`. -/
theorem two_mul_le_two_pow (k : ℕ) : 2 * k ≤ 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have h1 : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      rw [pow_succ]
      omega

/-- `2 ⌊log₂ n⌋ ≤ n`: with `k = ⌊log₂ n⌋`, `2k ≤ 2^k ≤ n` for `n ≥ 1`
(`Nat.pow_log_le_self`), and `⌊log₂ 0⌋ = 0`. Hence `n ≤ 2 (n − ⌊log₂ n⌋)`, the polynomial
majorant of the parameter change `n − ⌊log₂ n⌋ ↦ n` of [PS10, Theorem 63.1]. -/
theorem two_mul_log_two_le (n : ℕ) : 2 * Nat.log 2 n ≤ n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (two_mul_le_two_pow _).trans (Nat.pow_log_le_self 2 hn.ne')

/-- A string of length `m` is the encoding of some `m`-bit string. -/
theorem exists_ofFn_eq_of_length {m : ℕ} {w : List Bool} (h : w.length = m) :
    ∃ x : Fin m → Bool, List.ofFn x = w :=
  ⟨fun i => w.get (Fin.cast h.symm i), List.ext_get (by simp [h]) fun i h₁ h₂ => by simp⟩

/-- Taking `p` bits of `w ++ 0^p` for `|w| ≤ p` appends `p − |w|` zeros to `w`. -/
theorem take_append_replicate_of_le {p : ℕ} {w : List Bool} (hw : w.length ≤ p) :
    (w ++ List.replicate p false).take p = w ++ List.replicate (p - w.length) false := by
  rw [List.take_append, List.take_of_length_le hw, List.take_replicate]
  congr 2
  omega

/-- **Zero-padded pairs with first components of equal length agree on the first component**
and on the padded second components: `⟨a, b⟩ ++ z = ⟨a', b'⟩ ++ z'` with `|a| = |a'|` forces
`a = a'` and `b ++ z = b' ++ z'` (the first `2|a| + 2` bits are the doubled first component
and the separator, `Turing.pairEncode_eq_dbl`; `pairEncode_injective` on `⟨a, []⟩`). -/
theorem pairEncode_append_eq {a a' b b' z z' : List Bool} (ha : a.length = a'.length)
    (h : pairEncode a b ++ z = pairEncode a' b' ++ z') : a = a' ∧ b ++ z = b' ++ z' := by
  rw [pairEncode_eq_dbl, pairEncode_eq_dbl, List.append_assoc, List.append_assoc,
    List.append_assoc, List.append_assoc] at h
  have hlen : (dbl a).length = (dbl a').length := by simp [ha]
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  refine ⟨?_, List.append_cancel_left h2⟩
  have h3 : pairEncode a [] = pairEncode a' [] := by
    rw [pairEncode_eq_dbl, pairEncode_eq_dbl, h1]
  exact congrArg Prod.fst (@pairEncode_injective (a, []) (a', []) h3)

end TCSlib.Cryptography
