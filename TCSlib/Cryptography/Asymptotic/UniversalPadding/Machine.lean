/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.UniversalPadding.BinaryRoot
import TCSlib.Complexity.Randomized.UnaryPolynomial
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The linear-time multitape evaluator of Levin padding

The evaluator computes the shifted unary root, the unary data length, the source call and the padded result. Both polynomial computations are charged at their actual short arguments. Finite small inputs are absorbed into the running-time constant.

## Main definitions

The private linear-time predicate packages a multitape evaluator and its bound. Its closures use the existing timed machine combinators.

## Main results

* `TCSlib.Cryptography.PadQuad.exists_linearTime_padded` computes the padded word formula in linear time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010. (§2.13, Lemma 64.3.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.2, multitape machines, and §7.2, efficient arithmetic.)
-/

open Complexity Turing Turing.FinTM TCSlib.Cryptography Complexity.LogProg Complexity.BinArith

attribute [local irreducible] FinTM.ComputesFunInTime FinTM.ComputesInTime
attribute [local irreducible] PolyTimeComputable PadQuad.nu NUPPT.advInput
attribute [local irreducible] pairEncode pairDecode pairFstD pairSndD transduce

namespace TCSlib.Cryptography.PadQuad

/-- At the recovered parameter, the unary data length and the time of the call
to the original machine fit a linear budget in the padded input length. -/
private theorem levinTimeOnImage (ℓ : PolyExpr) (C c d n₁ : ℕ) (hd : 1 ≤ d)
    (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ B : ℕ, ∀ z : List Bool,
      let n := PadQuad.nu d z.length
      ℓ.eval n + C * ((NUPPT.advInput n (z.take (ℓ.eval n))).length + 1) ^ c ≤
        B * (z.length + 1) := by
  let B := ℓ.eval n₁ + C * (2 * n₁ + 3 + ℓ.eval n₁) ^ c + 1
  refine ⟨B, fun z => ?_⟩
  let n := PadQuad.nu d z.length
  change ℓ.eval n + C * ((NUPPT.advInput n (z.take (ℓ.eval n))).length + 1) ^ c ≤
    B * (z.length + 1)
  have hinput : (NUPPT.advInput n (z.take (ℓ.eval n))).length + 1 ≤
      2 * n + 3 + ℓ.eval n := by
    rw [NUPPT.length_advInput, List.length_take]
    omega
  have htime := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hinput c)
  by_cases hn : n₁ ≤ n
  · have hB : 1 ≤ B := by omega
    calc
      _ ≤ ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c := Nat.add_le_add_left htime _
      _ ≤ n ^ d := hdom n hn
      _ ≤ z.length := PadQuad.nu_pow_le hd _
      _ ≤ 1 * (z.length + 1) := by omega
      _ ≤ _ := Nat.mul_le_mul_right _ hB
  · have hn' : n ≤ n₁ := by omega
    have hℓ := ℓ.eval_mono hn'
    have harg : 2 * n + 3 + ℓ.eval n ≤ 2 * n₁ + 3 + ℓ.eval n₁ := by omega
    have hcost := Nat.mul_le_mul_left C (Nat.pow_le_pow_left harg c)
    calc
      _ ≤ ℓ.eval n₁ + C * (2 * n₁ + 3 + ℓ.eval n₁) ^ c :=
        Nat.add_le_add hℓ (htime.trans hcost)
      _ ≤ B := by omega
      _ ≤ _ := by simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left B (Nat.succ_le_succ (Nat.zero_le z.length))


/-- A word function has a deterministic multitape evaluator with a linear bound. -/
private def Linear (f : List Bool → List Bool) : Prop :=
  ∃ (M : FinTM Bool) (a : ℕ), M.ComputesFunInTime f (fun n => a * (n + 1))

/-- A machine for pointwise equal output computes the same function. -/
private theorem Linear.congr {f g : List Bool → List Bool} (hf : Linear f)
    (h : ∀ z, f z = g z) : Linear g := by
  rwa [← funext h]

/-- The output word fits the time bound because a step emits at most one bit. -/
private theorem length_le_time {M : FinTM Bool} {x y : List Bool} {t : ℕ}
    (h : M.ComputesInTime x y t) : y.length ≤ t := by
  rw [← ((computesInTime_iff _ _ _ _).1 h).2]
  exact M.tm.output_length_le x t

/-- Two-stage computation with both stages charged against the original input. -/
private theorem Linear.onImage {f g : List Bool → List Bool} (hf : Linear f)
    (U : FinTM Bool) (b : ℕ)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (b * (x.length + 1))) : Linear g := by
  obtain ⟨M, a, hM⟩ := hf
  obtain ⟨V, hV⟩ := exists_comp_on_image M U f g _ (fun n => b * (n + 1)) hM hU
  refine ⟨V, 2 * a + b + 2, (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  refine ((computesFunInTime_iff _ _ _).1 hV x).mono ?_
  rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc]
  have hpos : 1 ≤ x.length + 1 := by omega
  have htwo := Nat.mul_le_mul_left 2 hpos
  omega

/-- Linear-time functions compose since the first output also has linear length. -/
private theorem Linear.comp {f g : List Bool → List Bool}
    (hg : Linear g) (hf : Linear f) : Linear (fun x => g (f x)) := by
  obtain ⟨M, a, hM⟩ := hf
  obtain ⟨U, b, hU⟩ := hg
  refine Linear.onImage ⟨M, a, hM⟩ U (b * (a + 1)) fun x => ?_
  refine ((computesFunInTime_iff _ _ _).1 hU (f x)).mono ?_
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.one_mul]
  have hl := length_le_time ((computesFunInTime_iff _ _ _).1 hM x)
  omega

/-- Concatenation of two linear-time outputs is linear in the same input. -/
private theorem Linear.append {f g : List Bool → List Bool}
    (hf : Linear f) (hg : Linear g) : Linear (fun x => f x ++ g x) := by
  obtain ⟨M, a, hM⟩ := hf
  obtain ⟨U, b, hU⟩ := hg
  obtain ⟨V, c, hV⟩ := exists_append_computesFunInTime hM hU
  refine ⟨V, c * (a + b + 1), (computesFunInTime_iff _ _ _).2 fun x => ?_⟩
  apply ((computesFunInTime_iff _ _ _).1 hV x).mono
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

/-- Emit the doubled first component and separator, then the second component.
The prefix uses the timed payload map with the constant empty machine. -/
private theorem Linear.pair {f g : List Bool → List Bool} (hf : Linear f) (hg : Linear g) :
    Linear (fun x => pairEncode (f x) (g x)) := by
  have hdup : Linear (fun x => pairEncode x x) := computesFunInTime_pairDup
  obtain ⟨M, a, hM⟩ := hdup.comp hf
  obtain ⟨P, hP⟩ := exists_pairMapSnd_computesInTime (constTM [])
  have hprefix : Linear (fun x => pairEncode (f x) []) := by
    refine Linear.onImage ⟨M, a, hM⟩ P (40 * (a + 2)) fun x => ?_
    have h := hP (f x) (f x) [] 1 (constTM_computes [] (f x))
    refine h.mono ?_
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    rw [Nat.add_mul]
    have hl := length_le_time ((computesFunInTime_iff _ _ _).1 hM x)
    omega
  apply (hprefix.append hg).congr
  intro x
  simp only [pairEncode_eq, List.append_nil, List.append_assoc]

/-- The one-state copying transducer uses one input scan. -/
private theorem linear_id : Linear (fun x => x) := by
  let δ := fun (_ : Unit) (_ : Bool) => ()
  let o := fun (_ : Unit) (b : Bool) => some b
  have h : Linear (transduce δ o ()) :=
    ⟨transducerTM δ o (), 1, by
      simpa only [Nat.one_mul] using transducerTM_computes δ o ()⟩
  exact h.congr (transduce_of_copy δ o () (fun _ => rfl) (fun _ => rfl))

/-- The first projection is the published linear pair parser. -/
private theorem linear_fst : Linear pairFstD := by
  obtain ⟨M, a, hM⟩ := computesFunInTime_pairFst
  exact (show Linear _ from ⟨M, a, hM⟩).congr fun x => (pairFstD_eq x).symm

/-- The second projection is the published linear pair parser. -/
private theorem linear_snd : Linear pairSndD := by
  obtain ⟨M, a, hM⟩ := computesFunInTime_pairSnd
  exact (show Linear _ from ⟨M, a, hM⟩).congr fun x => (pairSndD_eq x).symm

/-- Interpret the first component's length as the position in the second. -/
private def split (z : List Bool) : List Bool :=
  match pairDecode z with
  | some (u, b) => pairEncode (b.take u.length) (b.drop u.length)
  | none => []

/-- The unary split is the existing randomized-computation primitive. -/
private theorem linear_split : Linear split := computesFunInTime_pairSplitAt

/-- On a well-formed pair the split returns the prefix and the suffix. -/
private theorem split_pair (u b : List Bool) :
    split (pairEncode u b) = pairEncode (b.take u.length) (b.drop u.length) := by
  simp only [split, pairDecode_pairEncode]

/-- A one-state transducer emits one zero per input cell. -/
private theorem linear_zeros : Linear (fun x => List.replicate x.length false) := by
  have h : Linear (transduce (fun (_ : Unit) _ => ()) (fun _ _ => some false) ()) :=
    ⟨transducerTM _ _ (), 1, by
      simpa only [Nat.one_mul] using transducerTM_computes
        (fun (_ : Unit) _ => ()) (fun _ _ => some false) ()⟩
  apply h.congr
  intro x
  induction x with
  | nil => rw [transduce_nil]; rfl
  | cons b x ih => rw [transduce_cons, ih]; rfl

/-- Two copies of the zero scan give exactly twice the input length. -/
private theorem linear_double_zeros : Linear (fun x => List.replicate (2 * x.length) false) :=
  (linear_zeros.append linear_zeros).congr fun x => by
    rw [Nat.two_mul, List.replicate_add]

/-- Prepending a true token costs one step beyond the copy scan. -/
private theorem linear_prepend_true : Linear (fun x => true :: x) :=
  ⟨prependTM [true], 2, (computesFunInTime_iff _ _ _).2 fun x => by
    refine ((computesFunInTime_iff _ _ _).1 (prependTM_computes [true]) x).mono ?_
    simp only [List.length_cons, List.length_nil]
    omega⟩

/-- A nonempty word has parameter at least one, so shifting and restoring the
unary root recovers the original parameter. -/
private theorem restored_root {d m : ℕ} (hd : 1 ≤ d) (hm : 1 ≤ m) :
    PadQuad.nu d m - 1 + 1 = PadQuad.nu d m := by
  have h := PadQuad.le_nu hd (n := 1) (by simpa only [one_pow] using hm)
  omega

/-- The charged unary length and call cost stay linear after the shift. The only
new case is the empty word, where the shifted parameter is one. -/
private theorem shifted_image_bound (ℓ : PolyExpr) {C c d n₁ : ℕ} (hd : 1 ≤ d)
    (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ B : ℕ, ∀ z : List Bool,
      let n := PadQuad.nu d z.length - 1 + 1
      ℓ.eval n + C * ((NUPPT.advInput n (z.take (ℓ.eval n))).length + 1) ^ c ≤
        B * (z.length + 1) := by
  obtain ⟨A, hA⟩ := levinTimeOnImage ℓ C c d n₁ hd hdom
  refine ⟨A + (ℓ.eval 1 + C * 5 ^ c), fun z => ?_⟩
  cases z with
  | nil =>
      have hn : PadQuad.nu d 0 = 0 := Nat.eq_zero_of_le_zero (PadQuad.nu_le _ _)
      simp only [List.length_nil, hn, Nat.zero_sub, Nat.zero_add, List.take_nil,
        NUPPT.length_advInput, Nat.mul_one, Nat.reduceAdd]
      omega
  | cons b z =>
      simp only [restored_root hd (by simp : 1 ≤ (b :: z).length)]
      exact (hA (b :: z)).trans (Nat.mul_le_mul_right _ (by omega))

/-- A linear-time evaluator for the shifted unary root suffices for the padded
function of [PS10, Lemma 64.3], with the original polynomial runtime bound on
the evaluator of the source function.

**Proof sketch.** Evaluate the length polynomial on the shifted root and
prepend a token to obtain the restored parameter. Split the input at the
unary length. Keep the suffix and a word of zeros while applying the source
evaluator to the encoded parameter and prefix. Concatenate the results and
cut at the length of the zero word. The sharper unary polynomial and payload
bounds charge both potentially superlinear calls against the original
input. At the empty input the final cut yields the empty word. -/
private theorem exists_linearTime_padded_of_shifted_root {F : List Bool → List Bool}
    {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F (fun k => C * (k + 1) ^ c)) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d)
    (hroot : ∃ (R : FinTM Bool) (a : ℕ), R.ComputesFunInTime
      (fun z => List.replicate (PadQuad.nu d z.length - 1) true) (fun m => a * (m + 1))) :
    ∃ (M' : FinTM Bool) (a : ℕ), M'.ComputesFunInTime
      (fun z =>
        ((z.drop (ℓ.eval (PadQuad.nu d z.length)) ++
          F (NUPPT.advInput (PadQuad.nu d z.length) (z.take (ℓ.eval (PadQuad.nu d z.length))))) ++
          List.replicate (2 * z.length) false).take (2 * z.length))
      (fun m => a * (m + 1)) := by
  let n (z : List Bool) := PadQuad.nu d z.length - 1 + 1
  let root (z : List Bool) := List.replicate (PadQuad.nu d z.length - 1) true
  let width (z : List Bool) := List.replicate (ℓ.eval (n z)) true
  let data (z : List Bool) := z.take (ℓ.eval (n z))
  let suffix (z : List Bool) := z.drop (ℓ.eval (n z))
  let zeros (z : List Bool) := List.replicate (2 * z.length) false
  let keep (z : List Bool) := pairEncode (zeros z) (suffix z)
  let arg (z : List Bool) := NUPPT.advInput (n z) (data z)
  obtain ⟨B, hB⟩ := shifted_image_bound ℓ hd hdom
  have hB' (z : List Bool) :
      ℓ.eval (n z) + C * ((arg z).length + 1) ^ c ≤ B * (z.length + 1) := hB z
  have hr : Linear root := hroot
  obtain ⟨P, p, hP⟩ := exists_unaryPoly_succ_computesFunInTime ℓ
  have hw : Linear width := by
    refine hr.onImage P (p * (B + 1)) fun z => ?_
    have h := (computesFunInTime_iff _ _ _).1 hP (root z)
    simp only [root, List.length_replicate] at h
    change P.ComputesInTime (root z) (width z) _
    refine h.mono ?_
    rw [Nat.mul_assoc, Nat.add_mul, Nat.one_mul]
    apply Nat.mul_le_mul_left
    have hcost := hB' z
    have hrootBound := PadQuad.nu_le d z.length
    change ℓ.eval (n z) + (PadQuad.nu d z.length - 1) + 1 ≤ _
    omega
  have hparam : Linear (fun z => List.replicate (n z) true) := by
    apply (linear_prepend_true.comp hr).congr
    intro z
    rw [show n z = (PadQuad.nu d z.length - 1) + 1 from rfl, List.replicate_succ]
  have hsplit : Linear (fun z => pairEncode (data z) (suffix z)) := by
    apply (linear_split.comp (hw.pair linear_id)).congr
    intro z
    rw [split_pair, show (width z).length = ℓ.eval (n z) from List.length_replicate]
  have hprefix : Linear data :=
    (linear_fst.comp hsplit).congr fun z => pairFstD_pairEncode _ _
  have hsuffix : Linear suffix :=
    (linear_snd.comp hsplit).congr fun z => pairSndD_pairEncode _ _
  have hkeep : Linear keep := linear_double_zeros.pair hsuffix
  have harg : Linear arg := (hparam.pair hprefix).congr fun z => (NUPPT.advInput_eq _ _).symm
  let stage (z : List Bool) := pairEncode (keep z) (arg z)
  let result (z : List Bool) := pairEncode (keep z) (F (arg z))
  obtain ⟨V, a, hV⟩ := hkeep.pair harg
  obtain ⟨Q, hQ⟩ := exists_pairMapSnd_computesInTime M
  have hresult : Linear result := by
    refine Linear.onImage (f := stage) ⟨V, a, hV⟩ Q (40 * (B + a + 1)) fun z => ?_
    have hF := (computesFunInTime_iff _ _ _).1 hM (arg z)
    refine (hQ (keep z) (arg z) _ _ hF).mono ?_
    rw [Nat.mul_assoc, Nat.add_mul, Nat.add_mul, Nat.one_mul]
    apply Nat.mul_le_mul_left
    have hlen : (stage z).length ≤ a * (z.length + 1) :=
      length_le_time ((computesFunInTime_iff _ _ _).1 hV z)
    have hcost := hB' z
    change C * ((arg z).length + 1) ^ c + (stage z).length + 1 ≤ _
    omega
  have hzero := (linear_fst.comp linear_fst).comp hresult
  have htail := (linear_snd.comp linear_fst).comp hresult
  have hvalue := linear_snd.comp hresult
  have hjoined := (htail.append hvalue).append hzero
  have hfinal := linear_fst.comp (linear_split.comp (hzero.pair hjoined))
  apply hfinal.congr
  intro z
  simp only [result, keep, pairFstD_pairEncode, pairSndD_pairEncode, split_pair,
    zeros, List.length_replicate]
  cases z with
  | nil => simp only [List.length_nil, Nat.mul_zero, List.take_zero]
  | cons b z =>
      simp only [data, suffix, arg, n,
        restored_root hd (by simp : 1 ≤ (b :: z).length)]


/-- In degree one the shifted root is the input length minus one. Emit one
true token for every bit following the first input bit. -/
private theorem linear_shifted_root_one :
    Linear (fun z => List.replicate (PadQuad.nu 1 z.length - 1) true) := by
  let δ := fun (_ : Bool) (_ : Bool) => true
  let emit := fun (seen : Bool) (_ : Bool) => if seen then some true else none
  have h : Linear (transduce δ emit false) :=
    ⟨transducerTM δ emit false, 1, by
      simpa only [Nat.one_mul] using transducerTM_computes δ emit false⟩
  have htrue (z : List Bool) : transduce δ emit true z = List.replicate z.length true := by
    induction z with
    | nil => rw [transduce_nil]; rfl
    | cons b z ih => rw [transduce_cons, show δ true b = true from rfl, ih]; rfl
  have hnu (m : ℕ) : PadQuad.nu 1 m = m :=
    le_antisymm (PadQuad.nu_le _ _) (PadQuad.le_nu le_rfl (by simp only [pow_one, le_refl]))
  apply h.congr
  intro z
  rw [hnu]
  cases z with
  | nil => rw [transduce_nil]; rfl
  | cons b z => rw [transduce_cons, show δ false b = true from rfl, htrue]; rfl

/-- In degree at least two the shifted root is small enough for a
quadratic budget in its numerical value. -/
private theorem shifted_root_sq_le {d : ℕ} (hd : 2 ≤ d) (m : ℕ) :
    (PadQuad.nu d m - 1 + 1) ^ 2 ≤ m + 1 := by
  by_cases hm : 1 ≤ m
  · rw [restored_root (by omega : 1 ≤ d) hm]
    have hpos : 0 < PadQuad.nu d m :=
      PadQuad.le_nu (by omega : 1 ≤ d) (n := 1) (by simpa only [one_pow] using hm)
    exact (Nat.pow_le_pow_right hpos hd).trans
      ((PadQuad.nu_pow_le (by omega : 1 ≤ d) m).trans (Nat.le_succ _))
  · have hm0 : m = 0 := by omega
    have hnu : PadQuad.nu d m = 0 := Nat.eq_zero_of_le_zero ((PadQuad.nu_le _ _).trans hm0.le)
    rw [hnu, hm0] <;> decide

/-- A multitape machine computes the shifted unary floor root in linear time.

**Proof sketch.** Degree one uses the single scan. For higher degrees,
compute the input length in binary and use the binary search on that word.
Its polynomial in the binary width is linear in the original length.
Convert the resulting canonical binary root to unary with the emitting
loop. On a canonical word the iteration count is linear in the represented
value and the polynomial in its width is also linear in that value.
The square of the shifted root, after restoring one, is bounded by the
original length plus one. -/
private theorem exists_linearTime_shifted_root (d : ℕ) (hd : 1 ≤ d) :
    ∃ (M : FinTM Bool) (a : ℕ),
      M.ComputesFunInTime (fun z => List.replicate (PadQuad.nu d z.length - 1) true)
        (fun m => a * (m + 1)) := by
  rcases eq_or_lt_of_le hd with he | hh
  · subst d
    exact linear_shifted_root_one
  · let v (z : List Bool) := PadQuad.nu d z.length - 1
    let enc (z : List Bool) := Nat.bits (v z)
    obtain ⟨L, a, hL⟩ := computesFunInTime_lengthBits
    obtain ⟨B, C, c, hB⟩ := (polyTimeComputable_iff _).1
      (polyTimeComputable_shifted_root d hd)
    obtain ⟨A, hA⟩ := exists_pow_width_bound c
    have henc : Linear enc := by
      refine Linear.onImage ⟨L, a, hL⟩ B (C * A) fun z => ?_
      have h := (computesFunInTime_iff _ _ _).1 hB (Nat.bits z.length)
      rw [bitsVal_bits] at h
      refine h.mono ?_
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left C (hA z.length)
    obtain ⟨U, K, k, hU⟩ := exists_binaryToUnary
    obtain ⟨H, hH⟩ := exists_pow_width_bound k
    refine henc.onImage U (K * H * 4) fun z => ?_
    have h := (computesFunInTime_iff _ _ _).1 hU (Nat.bits (v z))
    rw [bitsVal_bits] at h
    refine h.mono ?_
    have hcost := Nat.mul_le_mul_left K (hH (v z))
    have hwidth := two_pow_width_le (v z)
    have hR : 2 ^ (Nat.bits (v z)).length + 2 ≤ 4 * (v z + 1) := by omega
    calc K * ((Nat.bits (v z)).length + 1) ^ k * (2 ^ (Nat.bits (v z)).length + 2)
        ≤ K * (H * (v z + 1)) * (4 * (v z + 1)) := Nat.mul_le_mul hcost hR
      _ = K * H * 4 * (v z + 1) ^ 2 := by ring
      _ ≤ K * H * 4 * (z.length + 1) :=
        Nat.mul_le_mul_left _ (shifted_root_sq_le (by omega) z.length)

/-- The word formula of the Levin padded family has a linear-time evaluator.

**Proof sketch.** Combine the unary root construction with the padding
assembly, charging polynomial evaluation and the source call against the
original input length. [PS10, Lemma 64.3] -/
theorem exists_linearTime_padded {F : List Bool → List Bool} {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F (fun k => C * (k + 1) ^ c)) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ (M' : FinTM Bool) (a : ℕ), M'.ComputesFunInTime
      (fun z =>
        ((z.drop (ℓ.eval (PadQuad.nu d z.length)) ++
          F (NUPPT.advInput (PadQuad.nu d z.length) (z.take (ℓ.eval (PadQuad.nu d z.length))))) ++
          List.replicate (2 * z.length) false).take (2 * z.length))
      (fun m => a * (m + 1)) :=
  exists_linearTime_padded_of_shifted_root hM ℓ hd hdom (exists_linearTime_shifted_root d hd)


end TCSlib.Cryptography.PadQuad
