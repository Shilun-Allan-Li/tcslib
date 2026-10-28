/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import Mathlib.Data.Nat.Find

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The padded strong one-way function of Lemma 64.3

Proof infrastructure for [PS10, Lemma 64.3] (`TCSlib.Cryptography.lemma_64_3`): from a strong
one-way family `𝓕` with evaluator `F`, the padded family `PadQuad.family F ℓ d` with
`inLen = var`, `outLen = 2·var` and

`g'_m(y) = (y.drop ℓ(ν m) ++ F ⟨1^{ν m}, y.take ℓ(ν m)⟩) ++ 0^*` (`2m` bits),

where `ν m = max {n ≤ m : n^d ≤ m}` (`PadQuad.nu`) recovers the parameter from the input
length. For `d` dominating `ℓ`, `𝓕.outLen` and the running time of `F` (`exists_pow_dominates`),
the data block and the `F`-call fit in the input (`ℓ(ν m) + L(ν m) ≤ (ν m)^d ≤ m`), so the
padding is lossless and `g'` inherits one-wayness (`PadQuad.strongOneWay`, the reduction
`B(1^n, f(b)) = A'(1^m, ⟨a, f(b)⟩ padded).take ℓ(n)` with the padding sampled from the coins,
[Gar26, Lemma 2.3]); a linear-time multitape evaluator (`PadQuad.exists_linearTime_gStr`, the
only new machine, **admitted**) gives a quadratic-time one-work-tape binary machine through
`Turing.FinTM.one_work_tape_binary` and `Turing.exists_codeTM` (`PadQuad.quadraticCode_of_linear`).

**Deviation:** the text defines `g'` on lengths `m = n^c` only; here every length `m` is
handled through `ν` (data first, padding after, zero-filled to `2m` bits), see the docstring of
`TCSlib.Cryptography.lemma_64_3`.

## Main definitions

* `TCSlib.Cryptography.PadQuad.nu` — the parameter recovered from the input length;
  `TCSlib.Cryptography.PadQuad.raw`, `PadQuad.gStr`, `PadQuad.family` — the padded function.

## Main results

* `TCSlib.Cryptography.PadQuad.exists_pow_dominates` — `p(n) ≤ n^d` eventually.
* `TCSlib.Cryptography.PadQuad.easy_of_linear`, `PadQuad.quadraticCode_of_linear` — the two
  computability clauses from the linear-time evaluator.
* `TCSlib.Cryptography.PadQuad.exists_linearTime_gStr` — the linear-time evaluator (admitted).
* `TCSlib.Cryptography.PadQuad.strongOneWay`, `TCSlib.Cryptography.PadQuad.exists_family` —
  one-wayness of the padded family and the statement of [PS10, Lemma 64.3] with
  `QuadraticCode` unfolded.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13, Lemma 64.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3, padding).
-/

namespace TCSlib.Cryptography.PadQuad

open Complexity Turing TCSlib.Cryptography

/-! ## Polynomial domination and the parameter recovery -/

/-- Every syntactic polynomial is eventually dominated by a power: `p(n) ≤ n^d` for
`n ≥ n₁`, with `d ≥ 1` (`d := c + 1` and `n₁ := C 2^c + 1` for the majorant `C (n + 1)^c`). -/
theorem exists_pow_dominates (p : PolyExpr) : ∃ d n₁ : ℕ, 1 ≤ d ∧ ∀ n ≥ n₁, p.eval n ≤ n ^ d := by
  obtain ⟨C, c, h⟩ := p.eval_le
  refine ⟨c + 1, C * 2 ^ c + 1, by omega, fun n hn => ?_⟩
  calc p.eval n ≤ C * (n + 1) ^ c := h n
    _ ≤ C * (2 * n) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) c)
    _ = (C * 2 ^ c) * n ^ c := by rw [mul_pow]; ring
    _ ≤ n * n ^ c := Nat.mul_le_mul_right _ (by omega)
    _ = n ^ (c + 1) := by ring

/-- The parameter recovered from the input length `m`: the largest `n ≤ m` with `n^d ≤ m`
(`ν m = ⌊m^{1/d}⌋`). -/
def nu (d m : ℕ) : ℕ := Nat.findGreatest (fun n => n ^ d ≤ m) m

/-- `ν(m)^d ≤ m`. -/
theorem nu_pow_le {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : nu d m ^ d ≤ m :=
  Nat.findGreatest_spec (P := fun n => n ^ d ≤ m) (Nat.zero_le m)
    (by show 0 ^ d ≤ m; rw [Nat.zero_pow hd]; exact Nat.zero_le m)

/-- `ν(m) ≤ m`. -/
theorem nu_le (d m : ℕ) : nu d m ≤ m := Nat.findGreatest_le m

/-- `m < (ν(m) + 1)^d`: the recovered parameter is maximal. -/
theorem lt_succ_nu_pow {d : ℕ} (hd : 1 ≤ d) (m : ℕ) : m < (nu d m + 1) ^ d := by
  by_cases h : nu d m < m
  · have := Nat.findGreatest_is_greatest (P := fun n => n ^ d ≤ m) (n := m) (k := nu d m + 1)
      (Nat.lt_succ_self _) (by omega)
    exact not_le.mp this
  · have hm : nu d m = m := le_antisymm (nu_le d m) (not_lt.mp h)
    rw [hm]
    exact lt_of_lt_of_le (Nat.lt_succ_self m) (Nat.le_self_pow (by omega) _)

/-- `n ≤ ν(m)` whenever `n^d ≤ m`. -/
theorem le_nu {d : ℕ} (hd : 1 ≤ d) {n m : ℕ} (h : n ^ d ≤ m) : n ≤ nu d m :=
  Nat.le_findGreatest ((Nat.le_self_pow (by omega) n).trans h) h

/-! ## The padded function -/

/-- The raw output of `g'` on `z` (`|z| = m`, `n = ν m`): the padding block `z.drop ℓ(n)`
followed by `F ⟨1^n, z.take ℓ(n)⟩` (data first, so that the split is a `pairSplitAt`). -/
def raw (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) : List Bool :=
  z.drop (ℓ.eval (nu d z.length)) ++
    F (NUPPT.advInput (nu d z.length) (z.take (ℓ.eval (nu d z.length))))

/-- The string function of the padded family: the raw output zero-filled (or truncated) to
`2|z|` bits. -/
def gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) : List Bool :=
  (raw F ℓ d z ++ List.replicate (2 * z.length) false).take (2 * z.length)

/-- `gStr` has exactly `2|z|` bits. -/
theorem length_gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (z : List Bool) :
    (gStr F ℓ d z).length = 2 * z.length := by
  simp only [gStr, List.length_take, List.length_append, List.length_replicate]
  omega

/-- `gStr` is length-regular with output length `2·var`. -/
theorem lengthRegular_gStr (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) :
    FunFamily.LengthRegular (gStr F ℓ d) (.mul (.const 2) .var) := fun z => by
  simp [length_gStr]

/-- **The padded family** `g'` of [PS10, Lemma 64.3]: `FunFamily.ofString` of `gStr` with
output length `2·var` (so `inLen = var`). -/
def family (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) : FunFamily :=
  FunFamily.ofString (gStr F ℓ d) (.mul (.const 2) .var)

/-- The input length of the padded family is the parameter. -/
theorem family_inLen (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) :
    (family F ℓ d).inLen = .var := rfl

/-- The encoding of the padded family's value is `gStr`. -/
theorem ofFn_family_f (F : List Bool → List Bool) (ℓ : PolyExpr) (d : ℕ) (m : ℕ)
    (x : Fin m → Bool) : List.ofFn ((family F ℓ d).f m x) = gStr F ℓ d (List.ofFn x) :=
  FunFamily.ofFn_ofString_f (lengthRegular_gStr F ℓ d) m x

/-! ## The computability clauses -/

/-- **The linear-time evaluator of the padded family** [PS10, Lemma 64.3, "`g'` is computable
in time `O(n²)`"; the only new machine of the lemma] — **admitted**. Given a machine `M` for
`F` within `C (k + 1)^c` and `d` dominating the data length and the running time of `F` on
`⟨1^n, b⟩` (`hdom`), some multitape machine computes `gStr F ℓ d` in linear time.

**Proof sketch (construction).** On input `z` of length `m`: (1) the parameter `1^{ν m}` by
incremental unary counting — maintain `1^n` and the powers `1^{(n+1)^j}`, `j ≤ d`, on `d + 1`
tapes, advancing `n` while `1^{(n+1)^d}` fits in the input (the powers are updated by the
binomial identity, total cost `∑_{n ≤ ν m} O((n+1)^{d-1}) = O(m)`), or equivalently `d`-th root
extraction by consuming the input in chunks of sizes `(n+1)^d − n^d`; (2) `1^{ℓ(ν m)}` by
`Turing.FinTM.computesFunInTime_polyUnary` on the short string `1^{ν m}`, of cost
`O((ν m + 1)^{deg ℓ + 1}) ≤ O(m)` by `hdom` (through `Turing.FinTM.exists_comp_on_image`, which
charges the second stage at the original input length); (3) the split
`Turing.FinTM.computesFunInTime_pairSplitAt` on `⟨1^{ℓ(ν m)}, z⟩`; (4) the call of `M` on
`⟨1^{ν m}, z.take ℓ(ν m)⟩`, of cost `C (2 ν m + 3 + ℓ(ν m))^c ≤ (ν m)^d ≤ m` for `ν m ≥ n₁`
(finitely many smaller `m` are absorbed in the linear constant), again on the image; (5) the
concatenation `Turing.FinTM.computesFunInTime_pairConcat`, the zero filling (a one-state scan
of the input emitting two `false` per cell) and the cut to `2m` bits
(`pairSplitAt` on `⟨z ++ z, ·⟩`, `computesFunInTime_pairDup`/`pairConcat`). All stages are
linear or charged on short images, so the total is `c' (m + 1)`. -/
theorem exists_linearTime_gStr {F : List Bool → List Bool} {M : FinTM Bool} {C c : ℕ}
    (hM : M.ComputesFunInTime F fun k => C * (k + 1) ^ c) (ℓ : PolyExpr) {d n₁ : ℕ}
    (hd : 1 ≤ d) (hdom : ∀ n ≥ n₁, ℓ.eval n + C * (2 * n + 3 + ℓ.eval n) ^ c ≤ n ^ d) :
    ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1) := by
  sorry

/-- **`g'` is easy to compute** from a linear-time evaluator: the evaluator on `⟨1^m, y⟩`
applies `gStr` to the second component (`ofFn_family_f`). -/
theorem easy_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    (family F ℓ d).Easy := by
  have hg : PolyTimeComputable (gStr F ℓ d) := polyTimeComputable_of_linear h
  refine ⟨fun z => gStr F ℓ d (pairSndD z), hg.comp polyTimeComputable_pairSndD, fun m x => ?_⟩
  rw [ofFn_family_f]
  show gStr F ℓ d (pairSndD (pairEncode (List.replicate m true) (List.ofFn x))) = _
  rw [pairSndD_pairEncode]

/-- **`g'` is computable by a coded machine in quadratic time** from a linear-time multitape
evaluator: `Turing.FinTM.one_work_tape_binary` gives a one-work-tape binary machine within
`c₁ (c' (m + 1) + 1)² ≤ c₁ (c' + 1)² (m + 1)²`, and `Turing.exists_codeTM` a `CodeTM` with the
same runs. -/
theorem quadraticCode_of_linear {F : List Bool → List Bool} {ℓ : PolyExpr} {d : ℕ}
    (h : ∃ (M' : FinTM Bool) (c' : ℕ), M'.ComputesFunInTime (gStr F ℓ d) fun m => c' * (m + 1)) :
    ∃ (Mc : CodeTM) (c₀ : ℕ), ∀ m (x : Fin m → Bool),
      Mc.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn ((family F ℓ d).f m x))
        (c₀ * (m + 1) ^ 2) := by
  obtain ⟨M', c', hM'⟩ := h
  obtain ⟨M₁, c₁, hk, hM₁⟩ := FinTM.one_work_tape_binary M' _ _ hM'
  obtain ⟨Mc, hMc⟩ := exists_codeTM M₁ hk
  refine ⟨Mc, c₁ * (c' + 1) ^ 2, fun m x => ?_⟩
  rw [ofFn_family_f, hMc]
  refine (hM₁ (List.ofFn x)).mono ?_
  simp only [List.length_ofFn]
  calc c₁ * (c' * (m + 1) + 1) ^ 2 ≤ c₁ * ((c' + 1) * (m + 1)) ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by rw [Nat.add_mul, Nat.one_mul]; omega) 2)
    _ = c₁ * (c' + 1) ^ 2 * (m + 1) ^ 2 := by ring

/-! ## One-wayness of the padded family -/

/-- `List.ofFn` through a `finCongr` relabelling of the index type. -/
private theorem ofFn_arrowCongr {a b : ℕ} (h : a = b) (f : Fin a → Bool) :
    List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) f) = List.ofFn f :=
  (List.ofFn_congr h f).symm

/-- The encoding of a pair of strings assembled by `Fin.appendEquiv` (and a length cast) is
the concatenation of the encodings. -/
private theorem ofFn_appendEquiv {a b n : ℕ} (h : a + b = n) (q : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (((Fin.appendEquiv a b).trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
      List.ofFn q.1 ++ List.ofFn q.2 := by
  show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) (Fin.append q.1 q.2)) = _
  rw [ofFn_arrowCongr, List.ofFn_fin_append]

/-- The encoding of a coin string reassembled by `splitCoins` (and a length cast) is the
concatenation of the encodings of the halves. -/
private theorem ofFn_splitCoins_symm_cast {a b n : ℕ} (h : a + b = n)
    (q : (Fin a → Bool) × (Fin b → Bool)) :
    List.ofFn (((splitCoins a b).symm.trans (Equiv.arrowCongr (finCongr h) (Equiv.refl Bool))) q) =
      List.ofFn q.1 ++ List.ofFn q.2 := by
  show List.ofFn ((Equiv.arrowCongr (finCongr h) (Equiv.refl Bool)) ((splitCoins a b).symm q)) = _
  rw [ofFn_arrowCongr]
  obtain ⟨q₁, q₂⟩ := q
  exact ofFn_splitCoins_symm a b q₁ q₂

section Hardness

variable {𝓕 : FunFamily} {F : List Bool → List Bool}
  (hFx : ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x))
  {d : ℕ} (hd : 1 ≤ d)

include hFx in
/-- The raw output on `b ++ a` (`|b| = ℓ(n)`, `|a| = m − ℓ(n)`, `ν m = n`) is `a ++ f_n(b)`. -/
theorem raw_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (b : Fin (𝓕.inLen.eval n) → Bool) (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    raw F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) = List.ofFn a ++ List.ofFn (𝓕.f n b) := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  simp only [raw, hlen, hnu, List.take_left' (List.length_ofFn (f := b)),
    List.drop_left' (List.length_ofFn (f := b)), hFx]

include hFx in
/-- The padded output on `b ++ a` is `a ++ f_n(b)` followed by zeros (lossless padding, as
`(m − ℓ(n)) + L(n) ≤ 2m`). -/
theorem gStr_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (hL : 𝓕.outLen.eval n ≤ m) (b : Fin (𝓕.inLen.eval n) → Bool)
    (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) = (List.ofFn a ++ List.ofFn (𝓕.f n b)) ++
      List.replicate (2 * m - (List.ofFn a ++ List.ofFn (𝓕.f n b)).length) false := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  unfold gStr
  rw [raw_eq hFx hnu hℓ b a, hlen, take_append_replicate_of_le]
  simp only [List.length_append, List.length_ofFn]
  omega

include hFx in
/-- The challenge the reduction hands to the inverter of `g'`: the padding evaluator on
`⟨1^m, a ++ f_n(b)⟩` is the encoding of `g'_m(b ++ a)`. -/
theorem padStr_eq_gStr {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (b : Fin (𝓕.inLen.eval n) → Bool) (a : Fin (m - 𝓕.inLen.eval n) → Bool) :
    padStr (.mul (.const 2) .var) (List.replicate m true)
      (List.ofFn a ++ List.ofFn (𝓕.f n b)) = gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a) := by
  have hlen : (List.ofFn b ++ List.ofFn a).length = m := by
    simp only [List.length_append, List.length_ofFn]
    omega
  unfold padStr gStr
  rw [raw_eq hFx hnu hℓ b a, hlen]
  simp

include hFx in
/-- **Padding is injective on the data block**: equal padded outputs on `b' ++ a'` and
`b ++ a` force `f_n(b') = f_n(b)` (`List.append_inj` on the equal-length blocks). -/
theorem f_eq_of_gStr_eq {n m : ℕ} (hnu : nu d m = n) (hℓ : 𝓕.inLen.eval n ≤ m)
    (hL : 𝓕.outLen.eval n ≤ m) (b b' : Fin (𝓕.inLen.eval n) → Bool)
    (a a' : Fin (m - 𝓕.inLen.eval n) → Bool)
    (h : gStr F 𝓕.inLen d (List.ofFn b' ++ List.ofFn a') =
      gStr F 𝓕.inLen d (List.ofFn b ++ List.ofFn a)) : 𝓕.f n b' = 𝓕.f n b := by
  rw [gStr_eq hFx hnu hℓ hL b' a', gStr_eq hFx hnu hℓ hL b a, List.append_assoc,
    List.append_assoc] at h
  obtain ⟨-, h2⟩ := List.append_inj h (by simp)
  exact List.ofFn_injective (List.append_inj_left h2 (by simp))

include hFx in
/-- **The padding reduction wins** [Gar26, Lemma 2.3, machine form]: if `A` at parameter `n`
samples the padding `a` from its first `p(n)` coins, hands `A'` (at the length `m` with
`ν m = n`) the padded `⟨a, f_n(b)⟩` and returns the first `ℓ(n)` bits of the answer, then `A`
inverts `f` at `n` at least as often as `A'` inverts `g'` at `m`.

**Proof sketch.** `invProbAt_eq_uprob` on both sides. Split the uniform input of `g'` as
`(b, a)` (`Fin.appendEquiv`); split `A`'s coins as `((a, a''), (ρ, ρ''))` (`splitCoins`, with
`A'.coins m ≤ A'.coins (p n)` by `PolyExpr.eval_mono`); the extra coins `a'', ρ''` are unread
(`uprob_fst`). On `((b, a), ρ)`, `A`'s challenge to `A'` is `g'_m(b ++ a)` (`padStr_eq_gStr`),
so an answer `x' = b' ++ a'` of `A'` with `g'_m(x') = g'_m(b ++ a)` gives `A`'s answer `b'` with
`f_n(b') = f_n(b)` (`f_eq_of_gStr_eq`); conclude by `uprob_mono`. -/
theorem invProbAt_family_le (A' A : NUPPT) {n m : ℕ} (hnu : nu d m = n)
    (hℓ : 𝓕.inLen.eval n ≤ m) (hL : 𝓕.outLen.eval n ≤ m) {p : PolyExpr} (hm : m ≤ p.eval n)
    (hAc : A.coins = .add p (A'.coins.subst p))
    (hA : ∀ y (r : List Bool), A.runAtL n y r =
      (A'.runAtL m (padStr (.mul (.const 2) .var) (List.replicate m true)
        ((r.take (p.eval n)).take (m - 𝓕.inLen.eval n) ++ y))
        ((r.drop (p.eval n)).take (A'.coinLen m))).take (𝓕.inLen.eval n)) :
    (family F 𝓕.inLen d).invProbAt A' m ≤ 𝓕.invProbAt A n := by
  have hcast₁ : 𝓕.inLen.eval n + (m - 𝓕.inLen.eval n) = m := by omega
  let e : (Fin (𝓕.inLen.eval n) → Bool) × (Fin (m - 𝓕.inLen.eval n) → Bool) ≃ (Fin m → Bool) :=
    (Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hcast₁) (Equiv.refl Bool))
  have hofn : ∀ q, List.ofFn (e q) = List.ofFn q.1 ++ List.ofFn q.2 := fun q =>
    ofFn_appendEquiv hcast₁ q
  have hc₁ : A'.coinLen m ≤ A'.coinLen (p.eval n) := A'.coins.eval_mono hm
  have hcast₂ : (m - 𝓕.inLen.eval n) + (p.eval n - (m - 𝓕.inLen.eval n)) = p.eval n := by omega
  have hcast₃ : A'.coinLen m + (A'.coinLen (p.eval n) - A'.coinLen m) = A'.coinLen (p.eval n) := by
    omega
  have hcast₄ : p.eval n + A'.coinLen (p.eval n) = A.coinLen n := by
    simp [NUPPT.coinLen, hAc, PolyExpr.eval_subst]
  let eA : (Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ≃
      (Fin (p.eval n) → Bool) :=
    (splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₂) (Equiv.refl Bool))
  let eR : A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool) ≃
      (Fin (A'.coinLen (p.eval n)) → Bool) :=
    (splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₃) (Equiv.refl Bool))
  let eC : ((Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool)) ×
      (A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool)) ≃ A.Coins n :=
    (Equiv.prodCongr eA eR).trans
      ((splitCoins _ _).symm.trans (Equiv.arrowCongr (finCongr hcast₄) (Equiv.refl Bool)))
  have hofnC : ∀ q, List.ofFn (eC q) =
      (List.ofFn q.1.1 ++ List.ofFn q.1.2) ++ (List.ofFn q.2.1 ++ List.ofFn q.2.2) := by
    intro q
    show List.ofFn (((splitCoins _ _).symm.trans
      (Equiv.arrowCongr (finCongr hcast₄) (Equiv.refl Bool))) (eA q.1, eR q.2)) = _
    rw [ofFn_splitCoins_symm_cast]
    show List.ofFn (eA q.1) ++ List.ofFn (eR q.2) = _
    rw [ofFn_splitCoins_symm_cast, ofFn_splitCoins_symm_cast]
  let eArr : (((Fin (𝓕.inLen.eval n) → Bool) × (Fin (m - 𝓕.inLen.eval n) → Bool)) × A'.Coins m) ×
      ((Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ×
        (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool)) ≃
      (Fin (𝓕.inLen.eval n) → Bool) ×
        (((Fin (m - 𝓕.inLen.eval n) → Bool) × (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool)) ×
          (A'.Coins m × (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool))) :=
    (Equiv.prodProdProdComm _ _ _ _).trans
      ((Equiv.prodCongr (Equiv.prodAssoc _ _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob,
    ← uprob_comp_equiv (Equiv.prodCongr e (Equiv.refl (A'.Coins m))),
    ← uprob_comp_equiv (eArr.trans (Equiv.prodCongr (Equiv.refl _) eC))]
  rw [← uprob_fst (β := (Fin (p.eval n - (m - 𝓕.inLen.eval n)) → Bool) ×
    (Fin (A'.coinLen (p.eval n) - A'.coinLen m) → Bool))]
  refine uprob_mono fun q hq => ?_
  obtain ⟨x', hx', hgx'⟩ := hq
  -- the components of `q`
  obtain ⟨⟨⟨b, a⟩, ρ⟩, ⟨a'', ρ''⟩⟩ := q
  -- the answer of `A'`, split as `b' ++ a'`
  obtain ⟨⟨b', a'⟩, hx'e⟩ : ∃ q', e q' = x' := ⟨e.symm x', e.apply_symm_apply x'⟩
  refine ⟨b', ?_, ?_⟩
  · show A.runAt n (List.ofFn (𝓕.f n b)) (eC ((a, a''), (ρ, ρ''))) = List.ofFn b'
    rw [NUPPT.runAt_eq, hofnC, hA]
    simp only [List.take_left' (by simp; omega : (List.ofFn a ++ List.ofFn a'').length = p.eval n),
      List.drop_left' (by simp; omega : (List.ofFn a ++ List.ofFn a'').length = p.eval n),
      List.take_left' (List.length_ofFn (f := a)), List.take_left' (List.length_ofFn (f := ρ))]
    rw [padStr_eq_gStr hFx hnu hℓ b a, ← hofn (b, a), ← ofFn_family_f, ← NUPPT.runAt_eq]
    have hx'' : A'.runAt m (List.ofFn ((family F 𝓕.inLen d).f m (e (b, a)))) ρ = List.ofFn x' := hx'
    rw [hx'', ← hx'e, hofn, List.take_left' (List.length_ofFn (f := b'))]
  · show 𝓕.f n b' = 𝓕.f n b
    have hg : (family F 𝓕.inLen d).f m (e (b', a')) = (family F 𝓕.inLen d).f m (e (b, a)) := by
      rw [hx'e]; exact hgx'
    have hg' := congrArg List.ofFn hg
    rw [ofFn_family_f, ofFn_family_f, hofn, hofn] at hg'
    exact f_eq_of_gStr_eq hFx hnu hℓ hL b b' a a' hg'

include hFx hd in
/-- **The padded family is strongly one-way** [PS10, Lemma 64.3, "`g'` is strongly one-way"],
given a linear-time evaluator (`hlin`) and `d` dominating `ℓ + L` from `n₁` on (`hdom`).

**Proof sketch.** *Easy* is `easy_of_linear`. *Hard:* let `A'` invert `g'` with probability
`≥ 1/m^e` at infinitely many `m` (`not_negligible_iff`). Call `m` good when `m ≥ n₁^d`,
`m ≥ 1` and `A'` is that successful at `m`; `φ n` is a good `m` with `ν m = n` when one exists
(else `0`), majorised by `p := (n + 1)^d` (`lt_succ_nu_pow`). The reduction `A` is
`NUPPT.exists_reparam_pre_post_adv A' φ p` with advice `⟨⟨1^{φ n}, 1^{φ n − ℓ(n)}⟩, 1^{ℓ(n)}⟩`,
pre-processing `⟨y, a⟩ ↦ padStr (2·var) 1^{φ n} (a.take (φ n − ℓ(n)) ++ y)` and post-processing
"the first `ℓ(n)` bits", behind `NUPPT.exists_split _ p` which samples the padding `a` from
the first `p(n)` coins. For every good `m` with `n := ν m ≥ max(n₀, 2^{de}, n₁)`,
`invProbAt_family_le` at `m' := φ n` gives `1/n^{de+1} ≤ 1/(n+1)^{de} ≤ 1/m'^e ≤ invProbAt A' m'
≤ 𝓕.invProbAt A n`, contradicting `h.hard A` at the degree `de + 1`. -/
theorem strongOneWay (h : 𝓕.StrongOneWay) {n₁ : ℕ}
    (hdom : ∀ n ≥ n₁, 𝓕.inLen.eval n + 𝓕.outLen.eval n ≤ n ^ d)
    (hlin : ∃ (M' : FinTM Bool) (c' : ℕ),
      M'.ComputesFunInTime (gStr F 𝓕.inLen d) fun m => c' * (m + 1)) :
    (family F 𝓕.inLen d).StrongOneWay where
  easy := easy_of_linear hlin
  hard A' := by
    classical
    by_contra hneg
    obtain ⟨e, he⟩ := not_negligible_iff.mp hneg
    let good : ℕ → Prop := fun m => n₁ ^ d ≤ m ∧ 1 ≤ m ∧
      1 / (m : ℝ) ^ e ≤ (family F 𝓕.inLen d).invProbAt A' m
    let φ : ℕ → ℕ := fun n => if h : ∃ m, good m ∧ nu d m = n then h.choose else 0
    let p : PolyExpr := .pow (.add .var (.const 1)) d
    have hφ : ∀ n, φ n ≤ p.eval n := by
      intro n
      simp only [φ, p, PolyExpr.eval_pow, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      split_ifs with hex
      · have h1 := hex.choose_spec.2
        have h2 := lt_succ_nu_pow hd hex.choose
        rw [h1] at h2
        exact h2.le
      · exact Nat.zero_le _
    have hφ_spec : ∀ n, (∃ m, good m ∧ nu d m = n) → good (φ n) ∧ nu d (φ n) = n := by
      intro n hex
      simp only [φ, dif_pos hex]
      exact hex.choose_spec
    let β : ℕ → List Bool := fun n => pairEncode
      (pairEncode (List.replicate (φ n) true) (List.replicate (φ n - 𝓕.inLen.eval n) true))
      (List.replicate (𝓕.inLen.eval n) true)
    have hβ : ∀ n, (β n).length ≤
        (PolyExpr.add (.add (.mul (.const 6) p) (.const 6)) 𝓕.inLen).eval n := by
      intro n
      have h1 := hφ n
      simp only [β, length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
        PolyExpr.eval_const]
      omega
    have hpre : PolyTimeComputable fun w => padStr (.mul (.const 2) .var)
        (pairFstD (pairFstD (pairFstD w)))
        ((pairSndD (pairSndD w)).take (pairSndD (pairFstD (pairFstD w))).length ++
          pairFstD (pairSndD w)) := by
      have hu : PolyTimeComputable fun w => pairFstD (pairFstD (pairFstD w)) :=
        polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
      have hv : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
        polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
      have ha : PolyTimeComputable fun w => pairSndD (pairSndD w) :=
        polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
      have hy : PolyTimeComputable fun w => pairFstD (pairSndD w) :=
        polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
      have hcut : PolyTimeComputable fun w =>
          (pairSndD (pairSndD w)).take (pairSndD (pairFstD (pairFstD w))).length := by
        have h := (polyTimeComputable_pairTakePoly .var).comp (hv.pairEncode ha)
        convert h using 1
        funext w
        simp
      have h := (polyTimeComputable_padStr (.mul (.const 2) .var)).comp
        (hu.pairEncode (hcut.append hy))
      convert h using 1
      funext w
      simp
    have hpost : PolyTimeComputable fun w => (pairSndD w).take (pairSndD (pairFstD w)).length := by
      have h := (polyTimeComputable_pairTakePoly .var).comp
        ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
          polyTimeComputable_pairSndD)
      convert h using 1
      funext w
      simp
    obtain ⟨B, hBc, hB⟩ := A'.exists_reparam_pre_post_adv φ p hφ β _ hβ hpre hpost
    obtain ⟨A, hAc, -, hA⟩ := B.exists_split p
    have hA' : ∀ n y (r : List Bool), A.runAtL n y r =
        (A'.runAtL (φ n) (padStr (.mul (.const 2) .var) (List.replicate (φ n) true)
          ((r.take (p.eval n)).take (φ n - 𝓕.inLen.eval n) ++ y))
          ((r.drop (p.eval n)).take (A'.coinLen (φ n)))).take (𝓕.inLen.eval n) := by
      intro n y r
      rw [hA, hB]
      simp [β]
    -- the contradiction with the one-wayness of `𝓕` at degree `d e + 1`
    obtain ⟨n₀, hn₀⟩ := h.hard A (d * e + 1)
    obtain ⟨m, hm, hgm⟩ := he (max (max n₀ (2 ^ (d * e))) 1 ^ d + n₁ ^ d + 1)
    have hNd : max (max n₀ (2 ^ (d * e))) 1 ^ d ≤ m := by omega
    have hN : max (max n₀ (2 ^ (d * e))) 1 ≤ nu d m := le_nu hd hNd
    have hn₁ : n₁ ≤ nu d m := le_nu hd (by omega)
    have hgood : good m := ⟨by omega, by omega, by
      rwa [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hgm⟩
    obtain ⟨hgood', hnu'⟩ := hφ_spec (nu d m) ⟨m, hgood, rfl⟩
    -- notation: `n := nu d m`, `m' := φ n`
    have hn_n₀ : n₀ ≤ nu d m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hN)
    have hn_pow : 2 ^ (d * e) ≤ nu d m :=
      le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hN)
    have hn_one : 1 ≤ nu d m := le_trans (le_max_right _ _) hN
    have hℓL : 𝓕.inLen.eval (nu d m) + 𝓕.outLen.eval (nu d m) ≤ φ (nu d m) := by
      refine (hdom _ hn₁).trans ?_
      have h2 := nu_pow_le hd (φ (nu d m))
      rw [hnu'] at h2
      exact h2
    have hm'p : φ (nu d m) ≤ p.eval (nu d m) := hφ _
    have hAc' : A.coins = .add p (A'.coins.subst p) := by rw [hAc, hBc]
    have hcore := invProbAt_family_le hFx A' A hnu' (by omega) (by omega) hm'p hAc'
      (hA' (nu d m))
    have hbound := hn₀ (nu d m) hn_n₀
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)] at hbound
    have hsucc := hgood'.2.2
    -- real arithmetic: `1/n^(de+1) ≤ 1/(n+1)^(de) ≤ 1/m'^e`
    have hm'e : (φ (nu d m) : ℝ) ^ e ≤ ((nu d m : ℝ) + 1) ^ (d * e) := by
      have h1 : φ (nu d m) ^ e ≤ ((nu d m + 1) ^ d) ^ e := Nat.pow_le_pow_left hm'p e
      rw [← pow_mul] at h1
      exact_mod_cast h1
    have hnde : ((nu d m : ℝ) + 1) ^ (d * e) ≤ (nu d m : ℝ) ^ (d * e + 1) := by
      have h1 : (nu d m + 1) ^ (d * e) ≤ nu d m ^ (d * e + 1) := by
        calc (nu d m + 1) ^ (d * e) ≤ (2 * nu d m) ^ (d * e) :=
              Nat.pow_le_pow_left (by omega) _
          _ = 2 ^ (d * e) * nu d m ^ (d * e) := by rw [mul_pow]
          _ ≤ nu d m * nu d m ^ (d * e) := Nat.mul_le_mul_right _ hn_pow
          _ = nu d m ^ (d * e + 1) := by ring
      exact_mod_cast h1
    have hm'pos : (0 : ℝ) < (φ (nu d m) : ℝ) ^ e := by
      have : (1 : ℝ) ≤ (φ (nu d m) : ℝ) := by exact_mod_cast hgood'.2.1
      positivity
    have h1 : 1 / (nu d m : ℝ) ^ (d * e + 1) ≤ 1 / (φ (nu d m) : ℝ) ^ e :=
      one_div_le_one_div_of_le hm'pos (hm'e.trans hnde)
    linarith

end Hardness

/-- **[PS10, Lemma 64.3] with `QuadraticCode` unfolded**: from a strong one-way family, a
strong one-way family with `inLen = var` computable by a coded machine in time `c₀ (m + 1)²`
on the bare input — the padded family at the degree `d` of `exists_pow_dominates` applied to
`ℓ + L + (running time of the evaluator)`, given its linear-time evaluator
(`exists_linearTime_gStr`, admitted).

**Proof sketch.** `h.easy` gives `F` with machine `M` within `C (k + 1)^c`; dominate
`ℓ + L + C (2n + 3 + ℓ(n))^c` by `n^d` from `n₁` on (`exists_pow_dominates` on the syntactic
polynomial `add (add ℓ L) ((normal C c).subst (add (mul (const 2) var) (add (const 2) ℓ)))`);
`exists_linearTime_gStr` gives the linear evaluator; conclude with `strongOneWay` and
`quadraticCode_of_linear`. -/
theorem exists_family (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧
      ∃ (M : CodeTM) (c₀ : ℕ), ∀ n (x : Fin (𝓖.inLen.eval n) → Bool),
        M.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (𝓖.f n x))
          (c₀ * (𝓖.inLen.eval n + 1) ^ 2) := by
  obtain ⟨𝓕, h⟩ := h
  obtain ⟨F, ⟨M, C, c, hM⟩, hFx⟩ := h.easy
  obtain ⟨d, n₁, hd, hdom⟩ := exists_pow_dominates
    (.add (.add 𝓕.inLen 𝓕.outLen)
      ((PolyExpr.normal C c).subst (.add (.mul (.const 2) .var) (.add (.const 2) 𝓕.inLen))))
  have hdom₁ : ∀ n ≥ n₁, 𝓕.inLen.eval n + 𝓕.outLen.eval n ≤ n ^ d := fun n hn => by
    have := hdom n hn
    simp only [PolyExpr.eval_add] at this
    omega
  have hdom₂ : ∀ n ≥ n₁, 𝓕.inLen.eval n + C * (2 * n + 3 + 𝓕.inLen.eval n) ^ c ≤ n ^ d :=
    fun n hn => by
      have := hdom n hn
      simp only [PolyExpr.eval_add, PolyExpr.eval_subst, PolyExpr.eval_normal, PolyExpr.eval_mul,
        PolyExpr.eval_const, PolyExpr.eval_var] at this
      have h2 : C * (2 * n + 3 + 𝓕.inLen.eval n) ^ c = C * (2 * n + (2 + 𝓕.inLen.eval n) + 1) ^ c := by
        congr 2
        omega
      omega
  have hlin := exists_linearTime_gStr hM 𝓕.inLen hd hdom₂
  exact ⟨family F 𝓕.inLen d, family_inLen F 𝓕.inLen d, strongOneWay hFx hd h hdom₁ hlin,
    quadraticCode_of_linear hlin⟩


end TCSlib.Cryptography.PadQuad
