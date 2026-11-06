/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Candidates.Factoring
import TCSlib.Cryptography.NumberTheory.Units
import Mathlib.Data.Nat.Size

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# RSA: the RSA assumption, the RSA collection, RSA ⟹ factoring, RSA trapdoor permutations

The RSA material of [PS10, §2.9–§2.11]: the *RSA assumption* [PS10, Assumption 53.1]; the
collection `RSA = {f_{N,e}(x) = x^e mod N}` with indices `(N, e)`, `N = pq`, `e ∈ Z*_{Φ(N)}`,
domain `Z_N^*`, which is a collection of one-way functions under the RSA assumption
[PS10, Theorem 53.2] because `x ↦ x^e` permutes `Z_N^*` [PS10, Theorem 54.3]; the
implication RSA assumption ⟹ factoring assumption through the adversary `A'` of
[PS10, Algorithm 55.3] [PS10, Theorem 55.2]; and the trapdoor collection with
`Gen(1^n) = ((N, e), d)`, `ed ≡ 1 (mod Φ(N))`, `f⁻¹_{N,d}(y) = y^d mod N`
[PS10, Theorem 57.2].

Conventions (plan decisions D3–D5, D10, D11 and the decision log "Rabin/RSA scope"). The
modulus is `N = pq` for a uniform pair of *distinct* primes `p, q ∈ Π_n`
(`Candidates.DistinctPrimes`), so that `Φ(N) = (p−1)(q−1)`; the exponent `e` is uniform in
`Z*_{Φ(N)}` and `y` uniform in `Z_N^*`; the adversary receives `⟨1^n, ⟨N, ⟨e, y⟩⟩⟩` with
`2n`-bit numerals and its answer is read as a `2n`-bit numeral `x` with `x^e ≡ y (mod N)`.
Indices of the collection are the strings `⟨N, e⟩`; the domain at an index is `Z_N^*`
when the index is *valid* (`N ≠ 0`, `gcd(e, Φ(N)) = 1`) and the one-element group `Z_1^*`
otherwise, so that `f_{N,e}` is a permutation of the domain at *every* string index (the
frozen `PermCollection` quantifies over all strings) while the evaluator is one modular
exponentiation. The generator runs two truncated `SamplePrime` loops, falls back to the
pair `(2, 3)` when they fail or coincide, and samples `e` by rejection over bit strings of
the length of `Φ(N)` (`sampleUnitL`); the domain sampler samples `Z_N^*` the same way.
Every machine statement is conditional on the arithmetic bundle `ArithmeticFP`.

**Deviation:** Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n`
throughout; `p ≠ q` (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT
with `2^{-n}` failure. In particular the RSA assumption is stated on distinct primes (the
text's `Φ(N) = (p−1)(q−1)` needs `p ≠ q`, source error 5), the honest samplers are
truncated rejection samplers whose laws are within `rsaGenErr n` of the ideal ones (D10), the
generator outputs the trapdoor `⟨N, d⟩` (the inverter of Definition 56.1 receives the
trapdoor only), and at the degenerate parameters `n < 2` the generator works at `n = 2`.

## Main definitions

* `TCSlib.Cryptography.Candidates.rsaProb`, `TCSlib.Cryptography.Candidates.RSAAssumption`
  — [PS10, Assumption 53.1].
* `TCSlib.Cryptography.Candidates.rsaPerm` — the permutation `x ↦ x^e` of `Z_N^*`
  [PS10, Theorem 54.3].
* `TCSlib.Cryptography.Candidates.RSAParams`, `rsaGenParams`, `rsaGenRaw`, `rsaGen`,
  `sampleUnitL`, `unitSampleStr`, `rsaSampler`, `rsaInv` — the generator, domain sampler and
  trapdoor inverter.
* `TCSlib.Cryptography.Candidates.rsaTrapdoor` — the RSA collection of trapdoor permutations
  [PS10, Theorem 57.2]; `TCSlib.Cryptography.Candidates.rsaCollection` — its underlying
  collection [PS10, Theorem 53.2].
* `TCSlib.Cryptography.Candidates.rsaFromFactorStep`, `rsaFromFactorer` — the adversary
  `A'` of [PS10, Algorithm 55.3]; `rsaBreaker` — the RSA adversary of an inverter of the
  collection.

## Main results

* `TCSlib.Cryptography.Candidates.rsaPerm_symm_apply`, `pushesUniform_rsaPerm`
  [PS10, Theorem 54.3] (proved).
* `TCSlib.Cryptography.Candidates.rsaCollection_oneWay` [PS10, Theorem 53.2].
* `TCSlib.Cryptography.Candidates.rsa_imp_factoring` [PS10, Theorem 55.2];
  `rsaFromFactorStep_correct` — Algorithm 55.3 inverts whenever the factor is right (proved).
* `TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay` [PS10, Theorem 57.2].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.9: Assumption 53.1, Theorem 53.2, Theorem 54.3; §2.10: Theorem 55.2, Algorithm 55.3;
  §2.11: Definition 56.1, Theorem 57.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (the concrete inversion experiment).
-/

namespace TCSlib.Cryptography.Candidates

open Complexity Turing NumberTheory Finset

/-! ## The RSA assumption [PS10, Assumption 53.1] -/

/-- The input `⟨N, ⟨e, y⟩⟩` handed to the RSA adversary at parameter `n`: the modulus
`N = pq`, the exponent `e ∈ Z*_{Φ(N)}` and the challenge `y ∈ Z_N^*`, all as `2n`-bit
numerals [PS10, Assumption 53.1]. -/
def rsaInput (n : ℕ) (z : DistinctPrimes n) (e : (ZMod (Nat.totient (z.p * z.q)))ˣ)
    (y : (ZMod (z.p * z.q))ˣ) : List Bool :=
  pairEncode (natToList (2 * n) (z.p * z.q))
    (pairEncode (natToList (2 * n) (e : ZMod (Nat.totient (z.p * z.q))).val)
      (natToList (2 * n) (y : ZMod (z.p * z.q)).val))

/-- **The RSA experiment** [PS10, Assumption 53.1]:
`Pr[p, q ← Π_n, p ≠ q; N ← pq; e ← Z*_{Φ(N)}; y ← Z_N^*; x ← A(1^n, N, e, y) : x^e ≡ y (mod N)]`,
the average over the uniform pair of distinct primes of the probability, over `e`, `y` and
the coins of `A`, that the answer of `A` decodes to a `2n`-bit numeral `x` with
`x^e = y` in `Z_N`.

**Deviation:** distinct primes; `A` receives `1^n`; `2n`-bit numerals; wrong-length answers
fail (module docstring). -/
noncomputable def rsaProb (A : NUPPT) (n : ℕ) : ℝ :=
  uexp fun z : DistinctPrimes n =>
    uprob fun w : (ZMod (Nat.totient (z.p * z.q)))ˣ × ((ZMod (z.p * z.q))ˣ × A.Coins n) =>
      ∃ x : Fin (2 * n) → Bool,
        decodeFin (2 * n) (A.runAt n (rsaInput n z w.1 w.2.1) w.2.2) = some x ∧
          ((bitsToNat x : ℕ) : ZMod (z.p * z.q)) ^ (w.1 : ZMod (Nat.totient (z.p * z.q))).val =
            (w.2.1 : ZMod (z.p * z.q))

/-- **The RSA assumption** [PS10, Assumption 53.1]: every non-uniform PPT computes `e`-th
roots modulo a random `N = pq` with negligible probability.

**Deviation:** "`Pr[…] < ε(n)` for a negligible `ε`" is "`Pr[…]` is negligible"; see the
module docstring for the distribution and the input/output conventions. -/
def RSAAssumption : Prop := ∀ A : NUPPT, Negligible fun n => rsaProb A n

/-- Unfolding: the RSA assumption is the negligibility of every `rsaProb`. -/
theorem rsaAssumption_iff : RSAAssumption ↔ ∀ A : NUPPT, Negligible fun n => rsaProb A n :=
  Iff.rfl

/-- The RSA probability is nonnegative. -/
theorem rsaProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ rsaProb A n := by
  unfold rsaProb
  rw [uexp_def]
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The RSA probability is at most one. -/
theorem rsaProb_le_one (A : NUPPT) (n : ℕ) : rsaProb A n ≤ 1 := by
  rcases isEmpty_or_nonempty (DistinctPrimes n) with h | h
  · unfold rsaProb
    rw [uexp_def]
    simp
  · unfold rsaProb
    exact (OneWay.uexp_mono fun z => uprob_le_one _).trans (OneWay.uexp_const 1).le

/-- At the degenerate parameters `n < 2` the RSA experiment is empty. -/
theorem rsaProb_eq_zero_of_lt (A : NUPPT) {n : ℕ} (hn : n < 2) : rsaProb A n = 0 := by
  haveI := DistinctPrimes.isEmpty_of_lt hn
  unfold rsaProb
  rw [uexp_def]
  simp

/-! ## The RSA permutation [PS10, Theorem 54.3] -/

/-- **`x ↦ x^e` is a permutation of `Z_N^*`** [PS10, Theorem 54.3] for `e` coprime to
`Φ(N)`, packaged as an `Equiv` (`NumberTheory.rsa_pow_bijective`). -/
noncomputable def rsaPerm (N e : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N)) :
    (ZMod N)ˣ ≃ (ZMod N)ˣ :=
  Equiv.ofBijective (fun x => x ^ e) (rsa_pow_bijective he)

/-- `rsaPerm` is `x ↦ x^e`. -/
@[simp] theorem rsaPerm_apply (N e : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N))
    (x : (ZMod N)ˣ) : rsaPerm N e he x = x ^ e := rfl

/-- **The inverse map is `y ↦ y^d`** [PS10, Theorem 54.3]: if `ed ≡ 1 (mod Φ(N))` then
`(rsaPerm N e)⁻¹ y = y^d`. -/
theorem rsaPerm_symm_apply (N e d : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N))
    (hed : e * d ≡ 1 [MOD Nat.totient N]) (y : (ZMod N)ˣ) :
    (rsaPerm N e he).symm y = y ^ d := by
  apply (rsaPerm N e he).injective
  rw [Equiv.apply_symm_apply, rsaPerm_apply, ← pow_mul, mul_comm, pow_mul]
  exact (rsa_pow_pow hed y).symm

/-- **`x ↦ x^e` pushes the uniform distribution on `Z_N^*` to itself** [PS10, proof of
Theorem 53.2: "the distributions `{(e, x^e)}` and `{(e, y)}` are identical"]. -/
theorem pushesUniform_rsaPerm (N e : ℕ) [NeZero N] (he : Nat.Coprime e (Nat.totient N)) :
    HardcoreBit.PushesUniform (fun x : (ZMod N)ˣ => x ^ e) :=
  HardcoreBit.pushesUniform_equiv (rsaPerm N e he)

/-- **The decryption exponent from the modular inverse**: for `gcd(e, Φ) = 1`,
`d := (e⁻¹ : Z_Φ).val` satisfies `ed ≡ 1 (mod Φ)` [PS10, Theorem 54.3, "let `d` be its
inverse"; computed by `ExtendedEuclid`, Algorithm 43.2]. -/
theorem mul_inv_val_modEq (e Φ : ℕ) (h : Nat.Coprime e Φ) :
    e * ((e : ZMod Φ)⁻¹).val ≡ 1 [MOD Φ] := by
  have h1 := ZMod.coe_mul_inv_eq_one e h
  have h2 := congrArg ZMod.val h1
  rw [ZMod.val_mul, ZMod.val_natCast, ZMod.val_one_eq_one_mod] at h2
  show e * ((e : ZMod Φ)⁻¹).val % Φ = 1 % Φ
  rw [Nat.mul_mod]
  rw [Nat.mul_mod, Nat.mod_mod] at h2
  exact h2

/-! ## Indices, domains and encodings of the RSA collection -/

/-- The modulus `N` read from the index `⟨N, e⟩`. -/
def rsaN (i : List Bool) : ℕ := listToNat (pairFstD i)

/-- The exponent `e` read from the index `⟨N, e⟩`. -/
def rsaE (i : List Bool) : ℕ := listToNat (pairSndD i)

/-- An index `⟨N, e⟩` is *valid* when `N ≠ 0` and `gcd(e, Φ(N)) = 1`, the condition under
which `x ↦ x^e` permutes `Z_N^*` [PS10, Theorem 54.3]. (Not efficiently decidable from the
index — the generator only ever outputs valid indices.) -/
def RSAValid (i : List Bool) : Prop := rsaN i ≠ 0 ∧ Nat.Coprime (rsaE i) (Nat.totient (rsaN i))

/-- Unfolding `RSAValid`: `⟨N, e⟩` is valid iff `N ≠ 0` and `gcd(e, Φ(N)) = 1`. -/
theorem rsaValid_iff (i : List Bool) :
    RSAValid i ↔ rsaN i ≠ 0 ∧ Nat.Coprime (rsaE i) (Nat.totient (rsaN i)) := Iff.rfl

instance : DecidablePred RSAValid := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The modulus of the domain at an index: `N` for a valid index, `1` otherwise (so that the
domain is always a finite group). -/
def rsaMod (i : List Bool) : ℕ := if RSAValid i then rsaN i else 1

instance (i : List Bool) : NeZero (rsaMod i) := by
  unfold rsaMod
  split_ifs with h
  · exact ⟨h.1⟩
  · exact ⟨one_ne_zero⟩

/-- `rsaMod` of a valid index is `N`. -/
theorem rsaMod_of_valid {i : List Bool} (h : RSAValid i) : rsaMod i = rsaN i := if_pos h

/-- `rsaMod` of an invalid index is `1`. -/
theorem rsaMod_of_not_valid {i : List Bool} (h : ¬ RSAValid i) : rsaMod i = 1 := if_neg h

/-- `rsaMod i ≤ 2^{|N|}` where `|N|` is the width of the modulus numeral. -/
theorem rsaMod_le (i : List Bool) : rsaMod i ≤ 2 ^ (pairFstD i).length := by
  unfold rsaMod
  split_ifs with h
  · exact (listToNat_lt_two_pow _).le
  · exact Nat.one_le_two_pow

/-- The residue of an element of the domain fits in the width of the modulus numeral. -/
theorem val_lt_two_pow (i : List Bool) (x : (ZMod (rsaMod i))ˣ) :
    (x : ZMod (rsaMod i)).val < 2 ^ (pairFstD i).length :=
  lt_of_lt_of_le (ZMod.val_lt _) (rsaMod_le i)

/-- The number encoding an element of the domain: its residue for a valid index, and the
canonical representative `1 mod N` of the one-element domain of an invalid index. -/
def rsaEncVal (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : ℕ :=
  if RSAValid i then (x : ZMod (rsaMod i)).val else 1 % rsaN i

/-- The string encoding of an element of `D_{⟨N, e⟩}`: `rsaEncVal` as a numeral of the width
of the modulus numeral. -/
def rsaEnc (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : List Bool :=
  natToList (pairFstD i).length (rsaEncVal i x)

/-- The decoder of `D_{⟨N, e⟩}`: for a valid index, a numeral of the right width reading as a
number below `N` coprime to `N` (`ZMod.unitOfCoprime`); for an invalid index, the canonical
string of the one-element domain. -/
def rsaDec (i : List Bool) (w : List Bool) : Option (ZMod (rsaMod i))ˣ :=
  if RSAValid i then
    if h : w.length = (pairFstD i).length ∧ listToNat w < rsaMod i ∧
        Nat.Coprime (listToNat w) (rsaMod i) then
      some (ZMod.unitOfCoprime (listToNat w) h.2.2)
    else none
  else if w = natToList (pairFstD i).length (1 % rsaN i) then some 1 else none

/-- `f_{N,e}(x) = x^e mod N` as a string function on the encoded element, mirroring the
evaluator `modExpStr` [PS10, Theorem 53.2]. -/
def rsaF (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : List Bool :=
  natToList (pairFstD i).length (listToNat (rsaEnc i x) ^ rsaE i % rsaN i)

/-- The evaluator of the RSA collection on `⟨⟨N, e⟩, x⟩`: one modular exponentiation
`modExpStr ⟨x, ⟨e, N⟩⟩` [PS10, Theorem 53.2, "requires only one modular exponentiation"]. -/
def rsaEval (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD z) (pairEncode (pairSndD (pairFstD z)) (pairFstD (pairFstD z))))

/-- The evaluator computes `rsaF` on encoded elements. -/
theorem rsaEval_spec (i : List Bool) (x : (ZMod (rsaMod i))ˣ) :
    rsaEval (pairEncode i (rsaEnc i x)) = rsaF i x := by
  simp [rsaEval, rsaF, rsaE, rsaN]

/-- The evaluator is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_rsaEval (H : ArithmeticFP) : PolyTimeComputable rsaEval :=
  H.modExp.comp (polyTimeComputable_pairSndD.pairEncode
    ((polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD).pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)))

/-- The permutation of `D_{⟨N, e⟩}`: `x ↦ x^e` [PS10, Theorem 54.3] for a valid index, the
identity of the one-element domain otherwise. -/
noncomputable def rsaPermAt (i : List Bool) : (ZMod (rsaMod i))ˣ ≃ (ZMod (rsaMod i))ˣ :=
  if hv : RSAValid i then
    rsaPerm (rsaMod i) (rsaE i) (by rw [rsaMod_of_valid hv]; exact hv.2)
  else Equiv.refl _

/-- **`f_{N,e}` is the encoded permutation** at every index (the clause `f_perm` of
`PermCollection`): `rsaF i x = rsaEnc i (rsaPermAt i x)`.

**Proof sketch.** Valid index: both sides are the numeral of `x.val^e mod N`
(`val_units_pow`, `listToNat_natToList`). Invalid index: the domain is `Z_1^*`, the
encoding is the canonical `1 mod N`, and `(1 mod N)^e mod N = 1 mod N` (both `0` when
`N = 1`, both `1` otherwise); the width-`0` case is trivial. -/
theorem rsaF_perm (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : rsaF i x = rsaEnc i (rsaPermAt i x) := by
  rcases Nat.eq_zero_or_pos (pairFstD i).length with hl | hl
  · simp [rsaF, rsaEnc, hl, natToList_zero]
  by_cases hv : RSAValid i
  · have hM : rsaMod i = rsaN i := rsaMod_of_valid hv
    have hlt := val_lt_two_pow i x
    simp only [rsaF, rsaEnc, rsaEncVal, if_pos hv, rsaPermAt, dif_pos hv, rsaPerm_apply,
      listToNat_natToList hlt, val_units_pow]
    congr 1
    exact congrArg (fun M => (x : ZMod (rsaMod i)).val ^ rsaE i % M) hM.symm
  · have h1 : 1 % rsaN i < 2 ^ (pairFstD i).length :=
      lt_of_le_of_lt (Nat.mod_le _ _) (Nat.one_lt_two_pow hl.ne')
    simp only [rsaF, rsaEnc, rsaEncVal, if_neg hv, rsaPermAt, dif_neg hv, Equiv.refl_apply,
      listToNat_natToList h1]
    congr 1
    rcases Nat.lt_or_ge (rsaN i) 2 with h2 | h2
    · interval_cases (rsaN i)
      · simp
      · simp [Nat.mod_one]
    · rw [Nat.mod_eq_of_lt (by omega : 1 < rsaN i), one_pow, Nat.mod_eq_of_lt (by omega : 1 < rsaN i)]

/-- **Decoding inverts encoding** (the clause `decD_encD` of `Collection`).

**Proof sketch.** Valid index: the encoding has the right width, reads as `x.val < N`
coprime to `N`, and `ZMod.unitOfCoprime x.val = x` (`ZMod.natCast_zmod_val`). Invalid index:
the domain `Z_1^*` is a singleton (`ZMod.subsingleton_iff`). -/
theorem rsaDec_rsaEnc (i : List Bool) (x : (ZMod (rsaMod i))ˣ) : rsaDec i (rsaEnc i x) = some x := by
  by_cases hv : RSAValid i
  · have hlt := val_lt_two_pow i x
    have hl : listToNat (rsaEnc i x) = (x : ZMod (rsaMod i)).val := by
      simp only [rsaEnc, rsaEncVal, if_pos hv]
      exact listToNat_natToList hlt
    rw [rsaDec, if_pos hv, dif_pos ⟨by simp [rsaEnc], by rw [hl]; exact ZMod.val_lt _,
      by rw [hl]; exact ZMod.val_coe_unit_coprime x⟩]
    congr 1
    ext
    simp [ZMod.coe_unitOfCoprime, hl]
  · haveI : Subsingleton (ZMod (rsaMod i)) := ZMod.subsingleton_iff.2 (rsaMod_of_not_valid hv)
    rw [rsaDec, if_neg hv, if_pos (by simp [rsaEnc, rsaEncVal, if_neg hv])]
    congr 1
    exact Units.ext (Subsingleton.elim _ _)

/-- **Decoding is canonical** (the clause `Collection.encD_decD` of `rsaTrapdoor`; gate 03b,
finding 1): a string that `rsaDec i` decodes to `x` is `rsaEnc i x`. At a valid index it is a
numeral of the modulus width reading as `x.val < N` (`natToList_val_natCast`); at an invalid
index it is the canonical string of `1 mod N`. -/
theorem rsaEnc_of_rsaDec {i w : List Bool} {x : (ZMod (rsaMod i))ˣ} (h : rsaDec i w = some x) :
    rsaEnc i x = w := by
  rw [rsaDec] at h
  split_ifs at h with hv hw hw'
  · rw [← Option.some.inj h, rsaEnc, rsaEncVal, if_pos hv, ZMod.coe_unitOfCoprime]
    exact natToList_val_natCast hw.1 hw.2.1
  · rw [← Option.some.inj h, rsaEnc, rsaEncVal, if_neg hv, hw']

/-! ## The generator, the domain sampler and the inverter -/

/-- The width `B(n) = 2(n + 2)` of a coin block of the rejection samplers (at least the bit
length of any modulus `N < 2^{2 max(n,2)}`). -/
def rsaBlock : PolyExpr := .mul (.const 2) (.add .var (.const 2))

/-- `rsaBlock` evaluates to `B(n) = 2(n + 2)`. -/
theorem eval_rsaBlock (n : ℕ) : rsaBlock.eval n = 2 * (n + 2) := rfl

/-- The number of trials `T(n) = (4n + 8) n` of the rejection samplers: with acceptance rate
at least `1/(2 ⌈log₂ N⌉) ≥ 1/(4n + 8)` per trial (`NumberTheory.le_totient_mul_log_succ`,
C9), the failure probability is at most `e^{-n}` (`one_sub_one_div_pow_le_exp_neg`). -/
def rsaTrials : PolyExpr := .mul (.add (.mul (.const 4) .var) (.const 8)) .var

/-- `rsaTrials` evaluates to `T(n) = (4n + 8) n`. -/
theorem eval_rsaTrials (n : ℕ) : rsaTrials.eval n = (4 * n + 8) * n := rfl

/-- The coins of the domain sampler: `T(n)` blocks of `B(n)` bits. -/
def rsaSampleCoins : PolyExpr := .mul rsaTrials rsaBlock

/-- `rsaSampleCoins` evaluates to `T(n) · B(n)`. -/
theorem eval_rsaSampleCoins (n : ℕ) : rsaSampleCoins.eval n = rsaTrials.eval n * rsaBlock.eval n :=
  rfl

/-- The coins of the generator: two `SamplePrime` runs and one unit sampler. -/
def rsaGenCoins : PolyExpr := .add (.mul (.const 2) samplePrimeCoins) rsaSampleCoins

/-- **Rejection sampling of a unit modulo `N`** from a coin list: `Candidates.rejectBlocksL`
with the acceptance test `v < N ∧ gcd(v, N) = 1` — `T` trials, trial `t` reading the first `k`
bits of the `t`-th block of `B` bits as a number `v`; `none` if every trial is rejected. With
`k` the bit length of `N`, the acceptance rate is `Φ(N)/2^k ≥ 1/(2k)` [PS10, Theorem 53.2,
"sample a random element from `Z*_{Φ(N)}`" and "the set `D_i` is also easy to sample"].
Repair (run-3 audit P7-6): an instance of the shared sampler (closeness:
`statClose_rejectBlocksL`); the function is unchanged. -/
def sampleUnitL (N k B T : ℕ) (r : List Bool) : Option ℕ :=
  rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r

/-- The defining equation of `sampleUnitL`: block rejection sampling with the test
`v < N ∧ gcd(v, N) = 1`, i.e.
`sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r`. -/
theorem sampleUnitL_eq (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl

/-- A sampled value is below `N` and coprime to `N`. -/
theorem sampleUnitL_spec {N k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleUnitL N k B T r = some v) :
    v < N ∧ Nat.Coprime v N :=
  (rejectBlocksL_spec h).1

/-- The default `1 mod N` passes the unit test: `1 % N < N` and `gcd(1 % N, N) = gcd(N, 1) = 1`
(`Nat.gcd_rec`). -/
private theorem rsa_one_mod_spec {N : ℕ} (hN : 0 < N) : 1 % N < N ∧ Nat.Coprime (1 % N) N := by
  refine ⟨Nat.mod_lt _ hN, ?_⟩
  rw [Nat.Coprime, ← Nat.gcd_rec]
  exact Nat.gcd_one_right N

/-- The fallback of the unit sampler is a unit: for `N > 0`, the value
`(sampleUnitL N k B T r).getD (1 % N)` is below `N` and coprime to `N` (`sampleUnitL_spec`, or
the default, `rsa_one_mod_spec`). -/
private theorem rsa_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
    (sampleUnitL N k B T r).getD (1 % N) < N ∧
      Nat.Coprime ((sampleUnitL N k B T r).getD (1 % N)) N := by
  cases h : sampleUnitL N k B T r with
  | some v =>
    rw [Option.getD_some]
    exact sampleUnitL_spec h
  | none =>
    rw [Option.getD_none]
    exact rsa_one_mod_spec hN

/-- The units of `Z_N` are the accepted values of the unit test below `2^k` (for `N ≤ 2^k`):
`x ↦ x.val`, with inverse `v ↦ ZMod.unitOfCoprime v` (`ZMod.val_lt`,
`ZMod.val_coe_unit_coprime`, `ZMod.natCast_zmod_val`, `ZMod.val_natCast`). -/
private def rsa_unitsEquiv (N k : ℕ) [NeZero N] (hk : N ≤ 2 ^ k) :
    (ZMod N)ˣ ≃ {v : Fin (2 ^ k) // (v : ℕ) < N ∧ Nat.Coprime (v : ℕ) N} where
  toFun x := ⟨⟨(x : ZMod N).val, (ZMod.val_lt _).trans_le hk⟩, ZMod.val_lt _,
    ZMod.val_coe_unit_coprime x⟩
  invFun e := ZMod.unitOfCoprime ((e : Fin (2 ^ k)) : ℕ) e.2.2
  left_inv x := by
    apply Units.ext
    show ((((x : ZMod N).val : ℕ) : ZMod N)) = x
    exact ZMod.natCast_zmod_val _
  right_inv e := by
    apply Subtype.ext
    apply Fin.ext
    show ((ZMod.unitOfCoprime ((e : Fin (2 ^ k)) : ℕ) e.2.2 : (ZMod N)ˣ) : ZMod N).val = e.1
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt e.2.1]

/-- The acceptance probability of the unit test on `k`-bit values is `Φ(N)/2^k` (for
`N ≤ 2^k`): the accepted values are in bijection with `Z_N^*` (`rsa_unitsEquiv`,
`ZMod.card_units_eq_totient`). -/
private theorem rsa_uprob_units (N k : ℕ) [NeZero N] (hk : N ≤ 2 ^ k) :
    uprob (fun v : Fin (2 ^ k) => (v : ℕ) < N ∧ Nat.Coprime (v : ℕ) N) =
      (Nat.totient N : ℝ) / 2 ^ k := by
  rw [uprob_def, ← Nat.card_congr (rsa_unitsEquiv N k hk), Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Fintype.card_fin]
  push_cast
  rfl

/-- **The acceptance rate of the unit sampler**: for `0 < N` of bit length `k = Nat.size N ≤
2(n + 2)`, `2^k ≤ Φ(N) · (4n + 8)`.

**Proof sketch.** `2^{k−1} ≤ N` by the minimality of `Nat.size` (`Nat.size_le`), and
`⌊log₂ N⌋ < k` (`Nat.pow_log_le_self`, `Nat.lt_size_self`); so
`2^k ≤ 2N ≤ 2 Φ(N)(⌊log₂ N⌋ + 1) ≤ 2 Φ(N) k ≤ Φ(N)(4n + 8)`
(`NumberTheory.le_totient_mul_log_succ`). -/
private theorem rsa_two_pow_size_le (n N : ℕ) (hN : 0 < N) (hk : Nat.size N ≤ 2 * (n + 2)) :
    2 ^ Nat.size N ≤ Nat.totient N * (4 * n + 8) := by
  have hpos : 0 < Nat.size N := Nat.size_pos.2 hN
  have h1 : 2 ^ (Nat.size N - 1) ≤ N := by
    by_contra h
    push_neg at h
    have := Nat.size_le.2 h
    omega
  have h2 : Nat.log 2 N < Nat.size N :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).1
      ((Nat.pow_log_le_self 2 hN.ne').trans_lt (Nat.lt_size_self N))
  have h3 := le_totient_mul_log_succ N hN
  calc 2 ^ Nat.size N = 2 * 2 ^ (Nat.size N - 1) := by
        rw [← pow_succ']
        congr 1
        omega
    _ ≤ 2 * N := by omega
    _ ≤ 2 * (Nat.totient N * (Nat.log 2 N + 1)) := by omega
    _ ≤ 2 * (Nat.totient N * (2 * (n + 2))) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
    _ = Nat.totient N * (4 * n + 8) := by ring

/-- **The unit sampler is close to uniform** [PS10, Theorem 53.2, "sample a random element from
`Z*_{Φ(N)}`" and "the set `D_i` is also easy to sample"]: for a modulus `N ≥ 1` of bit length
`k = Nat.size N ≤ B(n)`, the sampler `sampleUnitL N k B(n) T(n)` on `T(n) · B(n)` uniform coins,
with the fallback `1 mod N`, outputs a number within statistical distance `e^{-n}` of the
residue of a uniform unit of `Z_N`. Shared statement S3 of the factoring fill (decision D1 (A)):
used by `rsaCollection_sampleClose`, `rsaCollection_invProbAt_le` (step (i), at the modulus
`Φ(N)`) and the Rabin samplers and reductions (`Rabin.lean`).

**Proof sketch.** (1) `sampleUnitL N k B T` is `rejectBlocksL` with the test
`v < N ∧ Nat.Coprime v N` (`sampleUnitL_eq`); apply `statClose_rejectBlocksL` with `k ≤ B(n)`
(`hk`), `T = T(n)` and the default `d = 1 % N`, which passes the test (`Nat.mod_lt`; `1` is
coprime to `N`, and for `N = 1` the default `0` is coprime to `1`) and is below `2^k`
(`d < N < 2^k`, `Nat.lt_size_self`). It gives closeness `(1 − Pr_{v < 2^k}[v < N ∧ gcd(v, N) = 1])^{T(n)}` to the uniform element of
`{v : Fin (2^k) // v < N ∧ gcd(v, N) = 1}` read as a number. (2) Transport that target to
`x ↦ (x : ZMod N).val` on `(ZMod N)ˣ` along the value-preserving bijection
`{v : Fin (2^k) // v < N ∧ gcd(v, N) = 1} ≃ (ZMod N)ˣ` (`ZMod.unitOfCoprime`; inverse by
`ZMod.val_lt`, `ZMod.val_coe_unit_coprime`, and `N < 2^k`; `StatClose.comp_equiv_right`).
(3) The acceptance probability is `Φ(N)/2^k` (`uprob_eq_card_filter` and the same bijection).
`2^k ≤ 2N` by the minimality of `Nat.size` (`Nat.size_le`: `N < 2^{k−1}` would give
`Nat.size N ≤ k − 1`), and `N ≤ Φ(N) · (log₂ N + 1) ≤ Φ(N) · k`
(`NumberTheory.le_totient_mul_log_succ`; `2^{log₂ N} ≤ N < 2^k`, `Nat.pow_log_le_self`), so
`Φ(N)/2^k ≥ 1/(2k) ≥ 1/(4n + 8)` by `hk` and `B(n) = 2(n + 2)` (`eval_rsaBlock`). (4) Hence the
distance is at most `(1 − 1/(4n + 8))^{(4n + 8) n} ≤ e^{-n}` (`eval_rsaTrials`,
`one_sub_one_div_pow_le_exp_neg`); conclude by `StatClose.mono`. -/
theorem statClose_sampleUnitL (n N : ℕ) [NeZero N] (hk : Nat.size N ≤ rsaBlock.eval n) :
    StatClose (fun s : Fin (rsaSampleCoins.eval n) → Bool =>
        (sampleUnitL N (Nat.size N) (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)).getD
          (1 % N))
      (fun x : (ZMod N)ˣ => (x : ZMod N).val) (Real.exp (-(n : ℝ))) := by
  have hN : 0 < N := NeZero.pos N
  have hNk : N < 2 ^ Nat.size N := Nat.lt_size_self N
  -- (1) the shared block sampler, default `1 % N`
  have hd : 1 % N < N ∧ Nat.Coprime (1 % N) N := rsa_one_mod_spec hN
  have h1 := statClose_rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) (Nat.size N)
    (rsaBlock.eval n) (rsaTrials.eval n) hk hd (hd.1.trans hNk)
  -- (2) transport the target to the residues of the units of `Z_N`
  have h2 := h1.comp_equiv_right (rsa_unitsEquiv N (Nat.size N) hNk.le)
  -- (3) the acceptance rate is at least `1/(4n + 8)`
  have hacc : 1 / ((4 * n + 8 : ℕ) : ℝ) ≤
      uprob fun v : Fin (2 ^ Nat.size N) => (v : ℕ) < N ∧ Nat.Coprime (v : ℕ) N := by
    rw [rsa_uprob_units N (Nat.size N) hNk.le, div_le_div_iff₀ (by positivity) (by positivity),
      one_mul]
    exact_mod_cast rsa_two_pow_size_le n N hN (by rw [← eval_rsaBlock]; exact hk)
  -- (4) the tail bound
  have hpow : (1 - uprob fun v : Fin (2 ^ Nat.size N) => (v : ℕ) < N ∧ Nat.Coprime (v : ℕ) N) ^
      rsaTrials.eval n ≤ Real.exp (-(n : ℝ)) := by
    rw [eval_rsaTrials]
    calc _ ≤ (1 - 1 / ((4 * n + 8 : ℕ) : ℝ)) ^ ((4 * n + 8) * n) :=
          pow_le_pow_left₀ (sub_nonneg.2 (uprob_le_one _)) (by linarith) _
      _ ≤ _ := one_sub_one_div_pow_le_exp_neg _ _ (by omega)
  rw [eval_rsaSampleCoins]
  exact h2.mono hpow

/-- The string function of the domain sampler on the modulus numeral `w` at parameter `n`
with coins `r`: a unit modulo `N = listToNat w` by rejection (`sampleUnitL` with the bit
length `Nat.size N` of `N`), written as a numeral of the width of `w`; the fallback `1 mod N`
on failure. -/
def unitSampleStr (w : List Bool) (n : ℕ) (r : List Bool) : List Bool :=
  natToList w.length
    ((sampleUnitL (listToNat w) (Nat.size (listToNat w)) (rsaBlock.eval n) (rsaTrials.eval n) r).getD
      (1 % listToNat w))

/-- The defining equation of `unitSampleStr`: the sampled unit modulo `N = listToNat w`
(fallback `1 mod N`) as a numeral of the width of `w`,
`unitSampleStr w n r = ⟦(sampleUnitL N (Nat.size N) B(n) T(n) r).getD (1 % N)⟧_{|w|}`. -/
theorem unitSampleStr_eq (w : List Bool) (n : ℕ) (r : List Bool) :
    unitSampleStr w n r = natToList w.length
      ((sampleUnitL (listToNat w) (Nat.size (listToNat w)) (rsaBlock.eval n) (rsaTrials.eval n)
        r).getD (1 % listToNat w)) := rfl

/-- The parameters output by the RSA generator at parameter `m`: distinct primes `p, q ∈ Π_m`,
an exponent `e < Φ(N)` coprime to `Φ(N)` and its inverse `d < Φ(N)`, `ed ≡ 1 (mod Φ(N))`
[PS10, Theorem 57.2, `[(N, e), d] ← Gen(1^n)`]. -/
structure RSAParams (m : ℕ) where
  /-- The pair of distinct primes. -/
  z : DistinctPrimes m
  /-- The public exponent. -/
  e : ℕ
  /-- The trapdoor exponent. -/
  d : ℕ
  /-- `e < Φ(N)`. -/
  e_lt : e < Nat.totient (z.p * z.q)
  /-- `gcd(e, Φ(N)) = 1`. -/
  e_cop : Nat.Coprime e (Nat.totient (z.p * z.q))
  /-- `d < Φ(N)`. -/
  d_lt : d < Nat.totient (z.p * z.q)
  /-- `ed ≡ 1 (mod Φ(N))`. -/
  ed : e * d ≡ 1 [MOD Nat.totient (z.p * z.q)]

namespace RSAParams

variable {m : ℕ}

/-- The modulus `N = pq`. -/
def N (P : RSAParams m) : ℕ := P.z.p * P.z.q

/-- `N < 2^{2m}`. -/
theorem N_lt (P : RSAParams m) : P.N < 2 ^ (2 * m) := P.z.mul_lt

/-- `e < 2^{2m}`. -/
theorem e_lt_two_pow (P : RSAParams m) : P.e < 2 ^ (2 * m) :=
  lt_of_lt_of_le P.e_lt ((Nat.totient_le _).trans P.N_lt.le)

/-- `d < 2^{2m}`. -/
theorem d_lt_two_pow (P : RSAParams m) : P.d < 2 ^ (2 * m) :=
  lt_of_lt_of_le P.d_lt ((Nat.totient_le _).trans P.N_lt.le)

end RSAParams

/-- **The generator's computation** [PS10, Theorem 53.2, "generate two primes `p, q`,
multiply them to generate `N`, and … sample a random element from `Z*_{Φ(N)}`";
Theorem 57.2]: two truncated `SamplePrime(m)` runs on the first two coin segments
(`samplePrimeL`), the fallback `(2, 3)` unless both are primes below `2^m` and distinct,
then `e` by `sampleUnitL` modulo `Φ(N)` on the remaining coins (fallback `e = 1`) and
`d = e⁻¹ mod Φ(N)`. The primes are drawn from `Π_{max m 2}` (the fallback needs `m ≥ 2`). -/
def rsaGenParams (m : ℕ) (r : List Bool) : RSAParams (max m 2) :=
  let L := samplePrimeCoins.eval (max m 2)
  let p := listToNat (samplePrimeL (max m 2) (r.take L))
  let q := listToNat (samplePrimeL (max m 2) ((r.drop L).take L))
  let z : DistinctPrimes (max m 2) :=
    if h : p.Prime ∧ q.Prime ∧ p ≠ q ∧ p < 2 ^ max m 2 ∧ q < 2 ^ max m 2 then
      ⟨(⟨⟨p, h.2.2.2.1⟩, h.1⟩, ⟨⟨q, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩
    else DistinctPrimes.default (le_max_right _ _)
  let Φ := Nat.totient (z.p * z.q)
  let eo := sampleUnitL Φ (Nat.size Φ) (rsaBlock.eval (max m 2)) (rsaTrials.eval (max m 2))
    (r.drop (2 * L))
  have he : eo.getD 1 < Φ ∧ Nat.Coprime (eo.getD 1) Φ := by
    match heo : eo with
    | some v => exact sampleUnitL_spec heo
    | none => exact ⟨z.one_lt_totient, Nat.coprime_one_left _⟩
  { z := z
    e := eo.getD 1
    d := ((eo.getD 1 : ZMod Φ)⁻¹).val
    e_lt := he.1
    e_cop := he.2
    d_lt := ZMod.val_lt _
    ed := mul_inv_val_modEq _ _ he.2 }

/-- The index `⟨N, e⟩` of the parameters, with `2m`-bit numerals. -/
def rsaIndexOf (m : ℕ) (P : RSAParams m) : List Bool :=
  pairEncode (natToList (2 * m) P.N) (natToList (2 * m) P.e)

/-- The trapdoor `⟨N, d⟩` of the parameters, with `2m`-bit numerals. -/
def rsaTrapOf (m : ℕ) (P : RSAParams m) : List Bool :=
  pairEncode (natToList (2 * m) P.N) (natToList (2 * m) P.d)

/-- The modulus read from `rsaIndexOf` is `N`. -/
@[simp] theorem rsaN_indexOf (m : ℕ) (P : RSAParams m) : rsaN (rsaIndexOf m P) = P.N := by
  simp [rsaN, rsaIndexOf, listToNat_natToList P.N_lt]

/-- The exponent read from `rsaIndexOf` is `e`. -/
@[simp] theorem rsaE_indexOf (m : ℕ) (P : RSAParams m) : rsaE (rsaIndexOf m P) = P.e := by
  simp [rsaE, rsaIndexOf, listToNat_natToList P.e_lt_two_pow]

/-- Generated indices are valid. -/
theorem rsaValid_indexOf (m : ℕ) (P : RSAParams m) : RSAValid (rsaIndexOf m P) :=
  ⟨by rw [rsaN_indexOf]; exact NeZero.ne (P.z.p * P.z.q),
    by rw [rsaN_indexOf, rsaE_indexOf]; exact P.e_cop⟩

/-- The domain modulus at a generated index is `N`. -/
theorem rsaMod_indexOf (m : ℕ) (P : RSAParams m) : rsaMod (rsaIndexOf m P) = P.N := by
  rw [rsaMod_of_valid (rsaValid_indexOf m P), rsaN_indexOf]

/-- The output `⟨⟨N, e⟩, ⟨N, d⟩⟩` of the generator at parameter `m` on the coins `r`. -/
def rsaGenOut (m : ℕ) (r : List Bool) : List Bool :=
  pairEncode (rsaIndexOf _ (rsaGenParams m r)) (rsaTrapOf _ (rsaGenParams m r))

/-- The string function of the generator on the raw layout `⟨⟨⟨1^n, []⟩, α⟩, r⟩`:
`rsaGenOut` at the parameter `n` read from `1^n` on the coins. -/
def rsaGenRaw (z : List Bool) : List Bool := rsaGenOut (NUPPT.inParam z).length (NUPPT.inCoins z)

/-! ### The unit sampler as a trial loop (helpers of `polyTimeComputable_unitSampleStr`)

The loop is an instance of the public repetition host `polyTimeComputable_iterateFind`; its
state is `⟨⟨1^B, ⟨1^k, w⟩⟩, ⟨counter, coins⟩⟩` (the header, then a unary trial counter and the
remaining coins). The family follows the pattern of the discrete-log fill's private trial loop
(`dla_ss*`, `DiscreteLog.lean`), with the stride `B` read from the header and the unit test in
place of the comparison. -/

/-- The number read from `[true]` is `1`. -/
private theorem rsa_listToNat_one : listToNat [true] = 1 := by
  rw [listToNat_eq]
  rfl

/-- The empty numeral reads as `0`. -/
private theorem rsa_listToNat_nil : listToNat [] = 0 := by
  rw [listToNat_eq]
  rfl

/-- `List.findSome?` of a filter-and-map is `List.find?` followed by the map. -/
private theorem rsa_findSome?_ite {α β : Type*} (p : α → Prop) [DecidablePred p] (h : α → β)
    (l : List α) :
    l.findSome? (fun t => if p t then some (h t) else none) =
      (l.find? fun t => decide (p t)).map h := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    by_cases ha : p a
    · rw [if_pos ha, decide_eq_true ha]
      rfl
    · rw [if_neg ha, decide_eq_false ha, ih]

/-- A search over `[0, L)` whose test also demands `i < N` is the search over `[0, N)`, for
`N ≤ L`. -/
private theorem rsa_find?_range_lt (p : ℕ → Bool) {N L : ℕ} (hNL : N ≤ L) :
    (List.range L).find? (fun i => decide (i < N) && p i) = (List.range N).find? p := by
  have hcongr : ∀ l : List ℕ, (∀ i ∈ l, i < N) →
      l.find? (fun i => decide (i < N) && p i) = l.find? p := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
      intro hl
      rw [List.find?_cons, List.find?_cons, ih (fun i hi => hl i (List.mem_cons_of_mem a hi)),
        decide_eq_true (hl a List.mem_cons_self), Bool.true_and]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hNL
  rw [List.range_add, List.find?_append, hcongr _ (fun i hi => List.mem_range.1 hi)]
  have hnone : (List.map (fun x => N + x) (List.range d)).find?
      (fun i => decide (i < N) && p i) = none := by
    rw [List.find?_eq_none]
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    simp
  rw [hnone, Option.or_none]

/-- **The unit test by comparisons**: for `N = ⟦w⟧`, "`¬ (N ≤ v)`, and the `|w|`-bit numeral `g`
of `gcd(v, N)` reads `≤ 1` and `≥ 1`" is the test `v < N ∧ gcd(v, N) = 1` (for `v < N` the gcd
is at most `N < 2^{|w|}`, so `g` reads as the gcd). -/
private theorem rsa_unitTest_eq (v : ℕ) (w : List Bool) :
    (!(decide (listToNat w ≤ v)) &&
      decide (listToNat (natToList w.length (Nat.gcd v (listToNat w))) ≤ listToNat [true]) &&
      decide (listToNat [true] ≤ listToNat (natToList w.length (Nat.gcd v (listToNat w))))) =
      decide (v < listToNat w ∧ Nat.Coprime v (listToNat w)) := by
  rw [rsa_listToNat_one]
  by_cases h : v < listToNat w
  · have hg : Nat.gcd v (listToNat w) < 2 ^ w.length :=
      lt_of_le_of_lt (Nat.gcd_le_right _ (by omega)) (listToNat_lt_two_pow w)
    rw [listToNat_natToList hg]
    have h1 : ¬ listToNat w ≤ v := by omega
    by_cases h2 : Nat.gcd v (listToNat w) = 1
    · have : Nat.Coprime v (listToNat w) := h2
      simpa [h1, h2, h] using this
    · have : ¬ Nat.Coprime v (listToNat w) := h2
      simp only [h1, h, this, decide_false, Bool.not_false, Bool.true_and, and_false]
      by_cases h3 : Nat.gcd v (listToNat w) ≤ 1
      · have h4 : ¬ 1 ≤ Nat.gcd v (listToNat w) := by omega
        simp [h3, h4]
      · simp [h3]
  · have h1 : listToNat w ≤ v := by omega
    simp [h1, h]

/-- The start state of the trial loop on the raw layout `z` with modulus numeral `w = f z`:
`⟨⟨1^{B(n)}, ⟨1^k, w⟩⟩, ⟨1^{T(n)}, r⟩⟩` with `1^k = sizeStr w` the bit length of `⟦w⟧`. -/
private def rsa_usStart (f : List Bool → List Bool) (z : List Bool) : List Bool :=
  pairEncode
    (pairEncode (List.replicate (rsaBlock.eval (NUPPT.inParam z).length) true)
      (pairEncode (sizeStr (f z)) (f z)))
    (pairEncode (List.replicate (rsaTrials.eval (NUPPT.inParam z).length) true) (NUPPT.inCoins z))

/-- One trial step: keep the header, decrement the counter, drop one block of `B` coins. -/
private def rsa_usStep (x : List Bool) : List Bool :=
  pairEncode (pairFstD x)
    (pairEncode ((pairFstD (pairSndD x)).drop 1)
      ((pairSndD (pairSndD x)).drop (pairFstD (pairFstD x)).length))

/-- The current trial value: the first `k` bits of the remaining coins. -/
private def rsa_usBlock (x : List Bool) : List Bool :=
  (pairSndD (pairSndD x)).take (pairFstD (pairSndD (pairFstD x))).length

/-- The gcd numeral of the trial value and the modulus (`xgcdStr`, width of the modulus). -/
private def rsa_usGcd (x : List Bool) : List Bool :=
  pairFstD (xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x)))))

/-- The acceptance test: the counter is nonzero, the trial value is below `N`, and its gcd
with `N` reads `≤ 1` and `≥ 1`. -/
private def rsa_usAcc (x : List Bool) : Bool :=
  !(decide (pairFstD (pairSndD x) = [])) &&
    (!(decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))) &&
      decide (listToNat (rsa_usGcd x) ≤ listToNat [true]) &&
      decide (listToNat [true] ≤ listToNat (rsa_usGcd x)))

/-- The payload: a `true` marker, then the accepted block. -/
private def rsa_usOut (x : List Bool) : List Bool := [true] ++ rsa_usBlock x

/-- Composition of polynomial-time functions in applied form, `x ↦ g (f x)` (so that the
composite is stated up to `β` only, without `Function.comp`). -/
private theorem rsa_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
  hg.comp hf

/-- The step is polynomial-time (`polyTimeComputable_tail`, `polyTimeComputable_pairDropPoly`). -/
private theorem rsa_usStep_poly : PolyTimeComputable rsa_usStep := by
  have h := polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_tail.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
      ((polyTimeComputable_pairDropPoly .var).comp
        ((polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD).pairEncode
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))))
  convert h using 1
  funext x
  simp only [rsa_usStep, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- The trial value is polynomial-time (`polyTimeComputable_pairTakePoly`). -/
private theorem rsa_usBlock_poly : PolyTimeComputable rsa_usBlock := by
  have h := (polyTimeComputable_pairTakePoly .var).comp
    ((polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)).pairEncode
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  convert h using 1
  funext x
  simp only [rsa_usBlock, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- A comparison `[⟦a x⟧ ≤ ⟦b x⟧]` of two polynomial-time numerals is polynomial-time
(`H.le`, read through `leStr_pairEncode`). -/
private theorem rsa_le_poly (H : ArithmeticFP) {a b : List Bool → List Bool}
    (ha : PolyTimeComputable a) (hb : PolyTimeComputable b) :
    PolyTimeComputable fun x => [decide (listToNat (a x) ≤ listToNat (b x))] := by
  have h := H.le.comp (ha.pairEncode hb)
  have e : (leStr ∘ fun x => pairEncode (a x) (b x)) =
      fun x => [decide (listToNat (a x) ≤ listToNat (b x))] := by
    funext x
    rw [Function.comp_apply, leStr_pairEncode]
  rw [e] at h
  exact h

/-- The acceptance test is polynomial-time (`polyTimeComputable_isNil`, `H.le`, `H.xgcd`). -/
private theorem rsa_usAcc_poly (H : ArithmeticFP) :
    PolyTimeComputable fun x => [rsa_usAcc x] := by
  have hw : PolyTimeComputable fun x => pairSndD (pairSndD (pairFstD x)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have hx : PolyTimeComputable fun x =>
      xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x)))) :=
    rsa_comp H.xgcd (rsa_usBlock_poly.pairEncode hw)
  have hg' : PolyTimeComputable fun x =>
      pairFstD (xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x))))) :=
    rsa_comp polyTimeComputable_pairFstD hx
  have e : (fun x => pairFstD (xgcdStr (pairEncode (rsa_usBlock x)
      (pairSndD (pairSndD (pairFstD x)))))) = rsa_usGcd := by
    funext x
    rw [rsa_usGcd]
  have hg : PolyTimeComputable rsa_usGcd := by
    rw [← e]
    exact hg'
  have hc : PolyTimeComputable fun x => pairFstD (pairSndD x) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have t1 : PolyTimeComputable fun x => [decide (pairFstD (pairSndD x) = [])] :=
    rsa_comp polyTimeComputable_isNil hc
  have t1' : PolyTimeComputable fun x => [!decide (pairFstD (pairSndD x) = [])] :=
    polyTimeComputable_not (p := fun x => decide (pairFstD (pairSndD x) = [])) t1
  have t2 : PolyTimeComputable fun x =>
      [decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))] :=
    rsa_le_poly H hw rsa_usBlock_poly
  have t2' : PolyTimeComputable fun x =>
      [!decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))] :=
    polyTimeComputable_not
      (p := fun x => decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))) t2
  have t3 : PolyTimeComputable fun x => [decide (listToNat (rsa_usGcd x) ≤ listToNat [true])] :=
    rsa_le_poly H hg (polyTimeComputable_const [true])
  have t4 : PolyTimeComputable fun x => [decide (listToNat [true] ≤ listToNat (rsa_usGcd x))] :=
    rsa_le_poly H (polyTimeComputable_const [true]) hg
  have t23 := polyTimeComputable_and
    (p := fun x => !decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x)))
    (q := fun x => decide (listToNat (rsa_usGcd x) ≤ listToNat [true])) t2' t3
  have t234 := polyTimeComputable_and
    (p := fun x => !decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x)) &&
      decide (listToNat (rsa_usGcd x) ≤ listToNat [true]))
    (q := fun x => decide (listToNat [true] ≤ listToNat (rsa_usGcd x))) t23 t4
  exact polyTimeComputable_and (p := fun x => !decide (pairFstD (pairSndD x) = []))
    (q := fun x => !decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x)) &&
      decide (listToNat (rsa_usGcd x) ≤ listToNat [true]) &&
      decide (listToNat [true] ≤ listToNat (rsa_usGcd x))) t1' t234

/-- The payload is polynomial-time (`polyTimeComputable_prepend`). -/
private theorem rsa_usOut_poly : PolyTimeComputable rsa_usOut :=
  (polyTimeComputable_prepend [true]).comp rsa_usBlock_poly

/-- The orbit of the step from `⟨h, ⟨c, s⟩⟩`: after `i` trials the state is
`⟨h, ⟨c.drop i, s.drop (i · |fst h|)⟩⟩`. -/
private theorem rsa_usStep_iterate (h c s : List Bool) (i : ℕ) :
    rsa_usStep^[i] (pairEncode h (pairEncode c s)) =
      pairEncode h (pairEncode (c.drop i) (s.drop (i * (pairFstD h).length))) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [rsa_usStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
    rw [Nat.succ_mul]

/-- One step at most doubles the length: `|step x| ≤ 2|x| + 4`. -/
private theorem rsa_length_usStep_le (x : List Bool) :
    (rsa_usStep x).length ≤ 2 * x.length + 4 := by
  have h1 := StateLoop.length_pairFstD_add_pairSndD_le x
  have h2 := StateLoop.length_pairFstD_add_pairSndD_le (pairSndD x)
  simp only [rsa_usStep, length_pairEncode, List.length_drop]
  omega

/-- From the first step on the state is a well-formed state word, which only shrinks. -/
private theorem rsa_length_usStep_usStep_le (x : List Bool) :
    (rsa_usStep (rsa_usStep x)).length ≤ (rsa_usStep x).length := by
  simp only [rsa_usStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
    List.length_drop]
  omega

/-- The orbit bound `|step^[i] x| ≤ 2|x| + 4` demanded by the repetition lemma. -/
private theorem rsa_length_usStep_iterate_le (x : List Bool) (i : ℕ) :
    (rsa_usStep^[i] x).length ≤ 2 * x.length + 4 := by
  cases i with
  | zero => simp only [Function.iterate_zero, id]; omega
  | succ i =>
    induction i with
    | zero => exact rsa_length_usStep_le x
    | succ i ih =>
      rw [Function.iterate_succ_apply'] at ih ⊢
      rw [Function.iterate_succ_apply']
      exact (rsa_length_usStep_usStep_le _).trans ih


/-- The trial loop's result on a start state `x`: the payload of the first accepted state among
the first `|x| + 1` states of the orbit, `[]` if none is accepted (the function of the
repetition host `polyTimeComputable_iterateFind`, with its `match` written as `Option.elim`). -/
private def rsa_usLoop (x : List Bool) : List Bool :=
  ((List.range (x.length + 1)).find? (fun i => rsa_usAcc (rsa_usStep^[i] x))).elim []
    (fun i => rsa_usOut (rsa_usStep^[i] x))

/-- The trial loop is polynomial-time: an instance of the repetition host
`polyTimeComputable_iterateFind` (`R = var`, orbit bound `2|x| + 4`), its `match` read by
`split`. -/
private theorem rsa_usLoop_poly (H : ArithmeticFP) : PolyTimeComputable rsa_usLoop := by
  have hF := polyTimeComputable_iterateFind rsa_usStep_poly (rsa_usAcc_poly H) rsa_usOut_poly
    PolyExpr.var (PolyExpr.add (.mul (.const 2) .var) (.const 4)) (fun x i _ => by
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      exact rsa_length_usStep_iterate_le x i)
  refine (congrArg PolyTimeComputable (funext fun x => ?_)).mp hF
  rw [rsa_usLoop, PolyExpr.eval_var]
  split
  · next i h => rw [h, Option.elim_some]
  · next h => rw [h, Option.elim_none]

/-- **The trial loop computes the unit sampler**: on the start state of `z`, the search of the
repetition host finds a trial exactly when `sampleUnitL` accepts, and then its payload is the
marker followed by a block reading as the accepted value:
`sampleUnitL N k B(n) T(n) r` is `none` when the search fails, and `some ⟦b⟧` when the payload
is `true :: b`.

**Proof sketch.** After `i` steps the state is `⟨h, ⟨1^T.drop i, r.drop (i B)⟩⟩`
(`rsa_usStep_iterate`), so trial `i` reads `(r.drop (i B)).take k` and the test is
`i < T ∧ (v < N ∧ gcd(v, N) = 1)` (`rsa_unitTest_eq`, `xgcdStr_pairEncode`). The search over
`[0, |x| + 1) ⊇ [0, T)` is then the search over `[0, T)` (`rsa_find?_range_lt`), and
`sampleUnitL = rejectBlocksL` is that search followed by reading the block
(`rejectBlocksL_eq`, `rsa_findSome?_ite`). -/
private theorem rsa_usFind_eq (f : List Bool → List Bool) (z : List Bool) :
    sampleUnitL (listToNat (f z)) (Nat.size (listToNat (f z))) (rsaBlock.eval (NUPPT.inParam z).length)
        (rsaTrials.eval (NUPPT.inParam z).length) (NUPPT.inCoins z) =
      ((List.range ((rsa_usStart f z).length + 1)).find?
        (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z)))).map
          (fun i => listToNat (rsa_usBlock (rsa_usStep^[i] (rsa_usStart f z)))) := by
  set B := rsaBlock.eval (NUPPT.inParam z).length
  set T := rsaTrials.eval (NUPPT.inParam z).length
  set c := NUPPT.inCoins z
  set w := f z
  have hstart : rsa_usStart f z = pairEncode (pairEncode (List.replicate B true)
      (pairEncode (sizeStr w) w)) (pairEncode (List.replicate T true) c) := rfl
  let val : ℕ → ℕ := fun i => listToNat ((c.drop (i * B)).take (Nat.size (listToNat w)))
  have hblock : ∀ i, rsa_usBlock (rsa_usStep^[i] (rsa_usStart f z)) =
      (c.drop (i * B)).take (Nat.size (listToNat w)) := by
    intro i
    rw [hstart, rsa_usStep_iterate]
    simp only [rsa_usBlock, pairFstD_pairEncode, pairSndD_pairEncode, length_sizeStr,
      List.length_replicate]
  have hacc : ∀ i, rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z)) =
      (decide (i < T) && decide (val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w))) := by
    intro i
    have hb := hblock i
    rw [rsa_usAcc, rsa_usGcd, hb, ← rsa_unitTest_eq, hstart, rsa_usStep_iterate]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, xgcdStr_pairEncode, List.drop_eq_nil_iff,
      List.length_replicate]
    by_cases h1 : i < T
    · simp [h1, val]
    · simp [h1]
  have hrange : T ≤ (rsa_usStart f z).length + 1 := by
    rw [hstart]
    simp only [length_pairEncode, List.length_replicate]
    omega
  have hfind : (List.range ((rsa_usStart f z).length + 1)).find?
      (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z))) =
      (List.range T).find?
        (fun i => decide (val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w))) := by
    rw [show (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z))) =
      fun i => decide (i < T) &&
        decide (val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w)) from funext hacc]
    exact rsa_find?_range_lt _ hrange
  rw [hfind, sampleUnitL_eq, rejectBlocksL_eq,
    rsa_findSome?_ite (fun i => val i < listToNat w ∧ Nat.Coprime (val i) (listToNat w)) val]
  simp only [hblock]
  rfl

/-- The start state is polynomial-time (the layout projections, `H.size` for `1^k`,
`polyTimeComputable_unaryPoly` for `1^{B(n)}` and `1^{T(n)}`). -/
private theorem rsa_usStart_poly (H : ArithmeticFP) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) : PolyTimeComputable (rsa_usStart f) :=
  ((((polyTimeComputable_unaryPoly rsaBlock).comp NUPPT.polyTimeComputable_inParam).pairEncode
      ((H.size.comp hf).pairEncode hf)).pairEncode
    (((polyTimeComputable_unaryPoly rsaTrials).comp NUPPT.polyTimeComputable_inParam).pairEncode
      NUPPT.polyTimeComputable_inCoins))

/-- **The unit sampler is polynomial-time** (the proof of `polyTimeComputable_unitSampleStr`,
stated here so that the generator can use it): for a polynomial-time `f`,
`z ↦ unitSampleStr (f z) |inParam z| (inCoins z)` is polynomial-time (see the public statement
for the proof sketch). -/
private theorem rsa_ptc_unitSampleStr (H : ArithmeticFP) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
  -- the trial loop on the start state (the repetition host)
  have hL : PolyTimeComputable fun z => rsa_usLoop (rsa_usStart f z) :=
    rsa_comp (rsa_usLoop_poly H) (rsa_usStart_poly H hf)
  have hN : PolyTimeComputable fun z => [decide (rsa_usLoop (rsa_usStart f z) = [])] :=
    rsa_comp polyTimeComputable_isNil hL
  have hT : PolyTimeComputable fun z => (rsa_usLoop (rsa_usStart f z)).drop 1 :=
    rsa_comp polyTimeComputable_tail hL
  -- the value block: the accepted block (marker dropped), or `[true]` (the fallback `1`)
  have hG : PolyTimeComputable fun z => if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
      else (rsa_usLoop (rsa_usStart f z)).drop 1 :=
    polyTimeComputable_ite (p := fun z => decide (rsa_usLoop (rsa_usStart f z) = []))
      (f := fun _ => [true]) (g := fun z => (rsa_usLoop (rsa_usStart f z)).drop 1) hN
      (polyTimeComputable_const [true]) hT
  -- `⟦v mod N⟧_{|w|}` (`H.divMod`)
  have hq : PolyTimeComputable fun z => pairSndD (divModStr (pairEncode
      (if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
        else (rsa_usLoop (rsa_usStart f z)).drop 1) (f z))) :=
    rsa_comp polyTimeComputable_pairSndD (rsa_comp H.divMod (hG.pairEncode hf))
  have e : (fun z => pairSndD (divModStr (pairEncode
      (if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
        else (rsa_usLoop (rsa_usStart f z)).drop 1) (f z)))) =
      fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
    funext z
    rw [divModStr_pairEncode, pairSndD_pairEncode, unitSampleStr_eq, rsa_usFind_eq f z, rsa_usLoop]
    rcases hres : (List.range ((rsa_usStart f z).length + 1)).find?
        (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z))) with _ | i
    · rw [Option.elim_none, Option.map_none, Option.getD_none, if_pos (by rfl), rsa_listToNat_one]
    · have hE : listToNat (rsa_usBlock (rsa_usStep^[i] (rsa_usStart f z))) < listToNat (f z) := by
        have hs := rsa_usFind_eq f z
        rw [hres, Option.map_some] at hs
        exact (sampleUnitL_spec hs).1
      rw [Option.elim_some, Option.map_some, Option.getD_some, if_neg (by
        rw [rsa_usOut, List.singleton_append]; simp), rsa_usOut, List.singleton_append,
        List.drop_one, List.tail_cons, Nat.mod_eq_of_lt hE]
  rw [e] at hq
  exact hq

/-! ### The generator as a string computation (helpers of `polyTimeComputable_rsaGenRaw`)

On `y = ⟨1^M, r⟩` with `M = max n 2`: the two prime runs (S1), the validity test (`H.prime`,
`H.le`), the fallback words `⟦2⟧ = [true, false]`, `⟦3⟧ = [true, true]`, `N` and `Φ` (`H.mul`,
`H.sub`), the exponent (the unit sampler on a re-laid-out input), `d` (`H.xgcd`), and the
`2M`-bit numerals as remainders modulo the all-ones word `1^{2M}` (`H.divMod`). -/

/-- The all-ones numeral `1^k` reads as `2^k − 1`. -/
private theorem rsa_listToNat_ones (k : ℕ) : listToNat (List.replicate k true) = 2 ^ k - 1 := by
  induction k with
  | zero => rw [List.replicate_zero, rsa_listToNat_nil]; rfl
  | succ k ih =>
    rw [List.replicate_succ', listToNat_eq, List.foldl_append, ← listToNat_eq, ih]
    have := Nat.one_le_two_pow (n := k)
    simp only [List.foldl_cons, List.foldl_nil, if_true, pow_succ]
    omega

/-- The numeral `[true, false]` reads as `2`. -/
private theorem rsa_listToNat_two : listToNat [true, false] = 2 := by
  rw [listToNat_eq]
  rfl

/-- The numeral `[true, true]` reads as `3`. -/
private theorem rsa_listToNat_three : listToNat [true, true] = 3 := by
  rw [listToNat_eq]
  rfl

/-- The product numeral reads as the product: `⟦mulStr ⟨a, b⟩⟧ = ⟦a⟧ · ⟦b⟧`. -/
private theorem rsa_listToNat_mulStr (a b : List Bool) :
    listToNat (mulStr (pairEncode a b)) = listToNat a * listToNat b := by
  rw [mulStr_pairEncode, listToNat_natToList]
  rw [pow_add]
  exact Nat.mul_lt_mul'' (listToNat_lt_two_pow a) (listToNat_lt_two_pow b)

/-- **Width normalization**: the remainder of `⟦x⟧` modulo the all-ones word `1^k` is the
`k`-bit numeral of `⟦x⟧` when `⟦x⟧ < 2^k − 1`. -/
private theorem rsa_norm (x : List Bool) (k : ℕ) (h : listToNat x < 2 ^ k - 1) :
    pairSndD (divModStr (pairEncode x (List.replicate k true))) = natToList k (listToNat x) := by
  rw [divModStr_pairEncode, pairSndD_pairEncode, List.length_replicate, rsa_listToNat_ones,
    Nat.mod_eq_of_lt h]

/-- A function equal pointwise to a polynomial-time one is polynomial-time. -/
private theorem rsa_ptc_congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
    (e : ∀ x, f x = g x) : PolyTimeComputable g := by
  rw [show g = f from (funext e).symm]
  exact h

/-- The first prime run: `samplePrimeL M` on the first `L = 2M³` coins of `y = ⟨1^M, r⟩`. -/
private def rsa_gP (y : List Bool) : List Bool :=
  samplePrimeL (pairFstD y).length ((pairSndD y).take (samplePrimeCoins.eval (pairFstD y).length))

/-- The second prime run: `samplePrimeL M` on the next `L` coins of `y = ⟨1^M, r⟩`. -/
private def rsa_gQ (y : List Bool) : List Bool :=
  samplePrimeL (pairFstD y).length
    (((pairSndD y).drop (samplePrimeCoins.eval (pairFstD y).length)).take
      (samplePrimeCoins.eval (pairFstD y).length))

/-- The validity test of the two runs: both prime, distinct (two comparisons), and at most
`⟦1^M⟧ = 2^M − 1`. -/
private def rsa_gValid (y : List Bool) : Bool :=
  decide (listToNat (rsa_gP y)).Prime && (decide (listToNat (rsa_gQ y)).Prime &&
    (!(decide (listToNat (rsa_gP y) ≤ listToNat (rsa_gQ y)) &&
        decide (listToNat (rsa_gQ y) ≤ listToNat (rsa_gP y))) &&
      (decide (listToNat (rsa_gP y) ≤ listToNat (pairFstD y)) &&
        decide (listToNat (rsa_gQ y) ≤ listToNat (pairFstD y)))))

/-- The first prime word: the run if valid, the fallback `⟦2⟧` otherwise. -/
private def rsa_gPw (y : List Bool) : List Bool := if rsa_gValid y then rsa_gP y else [true, false]

/-- The second prime word: the run if valid, the fallback `⟦3⟧` otherwise. -/
private def rsa_gQw (y : List Bool) : List Bool := if rsa_gValid y then rsa_gQ y else [true, true]

/-- The word of `Φ = (p − 1)(q − 1)`. -/
private def rsa_gPhi (y : List Bool) : List Bool :=
  mulStr (pairEncode (subStr (pairEncode (rsa_gPw y) [true])) (subStr (pairEncode (rsa_gQw y) [true])))

/-- The exponent word: the unit sampler modulo `Φ` at parameter `M` on the coins after the two
prime runs. -/
private def rsa_gE (y : List Bool) : List Bool :=
  unitSampleStr (rsa_gPhi y) (pairFstD y).length
    ((pairSndD y).drop ((PolyExpr.mul (.const 2) samplePrimeCoins).eval (pairFstD y).length))

/-- The `2M`-bit normalization of a word: its remainder modulo `1^{2M}`. -/
private def rsa_gNorm (y x : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode x
    (List.replicate ((PolyExpr.mul (.const 2) .var).eval (pairFstD y).length) true)))

/-- The generator's output computed from `y = ⟨1^M, r⟩`:
`⟨⟨⟦N⟧_{2M}, ⟦e⟧_{2M}⟩, ⟨⟦N⟧_{2M}, ⟦d⟧_{2M}⟩⟩`. -/
private def rsa_genCore (y : List Bool) : List Bool :=
  pairEncode
    (pairEncode (rsa_gNorm y (mulStr (pairEncode (rsa_gPw y) (rsa_gQw y)))) (rsa_gNorm y (rsa_gE y)))
    (pairEncode (rsa_gNorm y (mulStr (pairEncode (rsa_gPw y) (rsa_gQw y))))
      (rsa_gNorm y (pairSndD (xgcdStr (pairEncode (rsa_gE y) (rsa_gPhi y))))))

/-- The first prime run is polynomial-time (S1 on `⟨1^M, r.take L⟩`). -/
private theorem rsa_gP_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gP := by
  have hA : PolyTimeComputable fun y => pairEncode (pairFstD y)
      ((pairSndD y).take (samplePrimeCoins.eval (pairFstD y).length)) :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairTakePoly samplePrimeCoins)
  refine rsa_ptc_congr (rsa_comp (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
  rw [pairFstD_pairEncode, pairSndD_pairEncode, rsa_gP]

/-- The second prime run is polynomial-time (S1 on `⟨1^M, (r.drop L).take L⟩`). -/
private theorem rsa_gQ_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gQ := by
  have hD : PolyTimeComputable fun y => pairEncode (pairFstD y)
      ((pairSndD y).drop (samplePrimeCoins.eval (pairFstD y).length)) :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairDropPoly samplePrimeCoins)
  have hT := rsa_comp (polyTimeComputable_pairTakePoly samplePrimeCoins) hD
  have hA := polyTimeComputable_pairFstD.pairEncode hT
  refine rsa_ptc_congr (rsa_comp (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [rsa_gQ]

/-- A primality test `[⟦a x⟧ prime]` of a polynomial-time word is polynomial-time (`H.prime`,
read through `primeStr_eq`). -/
private theorem rsa_prime_poly (H : ArithmeticFP) {a : List Bool → List Bool}
    (ha : PolyTimeComputable a) :
    PolyTimeComputable fun x => [decide (listToNat (a x)).Prime] := by
  have h := rsa_comp H.prime ha
  rw [primeStr_eq] at h
  exact h

/-- The validity test is polynomial-time. -/
private theorem rsa_gValid_poly (H : ArithmeticFP) : PolyTimeComputable fun y => [rsa_gValid y] := by
  have hP := rsa_gP_poly H
  have hQ := rsa_gQ_poly H
  have t1 := rsa_prime_poly H hP
  have t2 := rsa_prime_poly H hQ
  have t3 := rsa_le_poly H hP hQ
  have t4 := rsa_le_poly H hQ hP
  have t5 := rsa_le_poly H hP polyTimeComputable_pairFstD
  have t6 := rsa_le_poly H hQ polyTimeComputable_pairFstD
  have t34 := polyTimeComputable_not (polyTimeComputable_and
    (p := fun y => decide (listToNat (rsa_gP y) ≤ listToNat (rsa_gQ y)))
    (q := fun y => decide (listToNat (rsa_gQ y) ≤ listToNat (rsa_gP y))) t3 t4)
  have t56 := polyTimeComputable_and
    (p := fun y => decide (listToNat (rsa_gP y) ≤ listToNat (pairFstD y)))
    (q := fun y => decide (listToNat (rsa_gQ y) ≤ listToNat (pairFstD y))) t5 t6
  have t3456 := polyTimeComputable_and
    (p := fun y => !(decide (listToNat (rsa_gP y) ≤ listToNat (rsa_gQ y)) &&
        decide (listToNat (rsa_gQ y) ≤ listToNat (rsa_gP y))))
    (q := fun y => decide (listToNat (rsa_gP y) ≤ listToNat (pairFstD y)) &&
        decide (listToNat (rsa_gQ y) ≤ listToNat (pairFstD y))) t34 t56
  have t23456 := polyTimeComputable_and
    (p := fun y => decide (listToNat (rsa_gQ y)).Prime) t2 t3456
  have h := polyTimeComputable_and
    (p := fun y => decide (listToNat (rsa_gP y)).Prime) t1 t23456
  unfold rsa_gValid
  exact h

/-- The two prime words are polynomial-time (`polyTimeComputable_ite`). -/
private theorem rsa_gPw_poly (H : ArithmeticFP) :
    PolyTimeComputable rsa_gPw ∧ PolyTimeComputable rsa_gQw := by
  constructor
  · have h := polyTimeComputable_ite (p := rsa_gValid) (f := rsa_gP) (g := fun _ => [true, false])
      (rsa_gValid_poly H) (rsa_gP_poly H) (polyTimeComputable_const _)
    unfold rsa_gPw
    exact h
  · have h := polyTimeComputable_ite (p := rsa_gValid) (f := rsa_gQ) (g := fun _ => [true, true])
      (rsa_gValid_poly H) (rsa_gQ_poly H) (polyTimeComputable_const _)
    unfold rsa_gQw
    exact h

/-- The word of `Φ` is polynomial-time (`H.sub`, `H.mul`). -/
private theorem rsa_gPhi_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gPhi := by
  have h1 := rsa_comp H.sub ((rsa_gPw_poly H).1.pairEncode (polyTimeComputable_const [true]))
  have h2 := rsa_comp H.sub ((rsa_gPw_poly H).2.pairEncode (polyTimeComputable_const [true]))
  have h := rsa_comp H.mul (h1.pairEncode h2)
  unfold rsa_gPhi
  exact h

/-- The exponent word is polynomial-time: the unit sampler on the re-laid-out input
`layout 1^M ⟦Φ⟧ [] (r.drop 2L)` (`rsa_ptc_unitSampleStr`, `NUPPT.polyTimeComputable_layout`). -/
private theorem rsa_gE_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gE := by
  have hl := NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD (rsa_gPhi_poly H)
    (polyTimeComputable_const []) (polyTimeComputable_pairDropPoly (.mul (.const 2) samplePrimeCoins))
  refine rsa_ptc_congr (rsa_comp (rsa_ptc_unitSampleStr H NUPPT.polyTimeComputable_inArg) hl)
    fun y => ?_
  rw [NUPPT.inArg_layout, NUPPT.inParam_layout, NUPPT.inCoins_layout, rsa_gE]

/-- The normalization of a polynomial-time word is polynomial-time (`H.divMod`,
`polyTimeComputable_unaryPoly`). -/
private theorem rsa_gNorm_poly (H : ArithmeticFP) {x : List Bool → List Bool}
    (hx : PolyTimeComputable x) : PolyTimeComputable fun y => rsa_gNorm y (x y) := by
  have ho := rsa_comp (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) polyTimeComputable_pairFstD
  have h := rsa_comp polyTimeComputable_pairSndD (rsa_comp H.divMod (hx.pairEncode ho))
  unfold rsa_gNorm
  exact h

/-- The generator's string computation is polynomial-time. -/
private theorem rsa_genCore_poly (H : ArithmeticFP) : PolyTimeComputable rsa_genCore := by
  have hN := rsa_comp H.mul ((rsa_gPw_poly H).1.pairEncode (rsa_gPw_poly H).2)
  have hD := rsa_comp polyTimeComputable_pairSndD
    (rsa_comp H.xgcd ((rsa_gE_poly H).pairEncode (rsa_gPhi_poly H)))
  have h := ((rsa_gNorm_poly H hN).pairEncode (rsa_gNorm_poly H (rsa_gE_poly H))).pairEncode
    ((rsa_gNorm_poly H hN).pairEncode (rsa_gNorm_poly H hD))
  unfold rsa_genCore
  exact h

/-- **The string computation is the generator**: on `⟨1^{max n 2}, r⟩` it outputs
`rsaGenOut n r`.

**Proof sketch.** With `M = max n 2` and `L = 2M³`, `rsa_gP`, `rsa_gQ` are the two prime runs
of `rsaGenParams`, and the validity test is its condition (`⟦1^M⟧ = 2^M − 1`; two comparisons
for `p ≠ q`), so the prime words read as the primes of the parameters (`default_p`,
`default_q` on the fallback). Then `⟦N⟧ = pq` (`rsa_listToNat_mulStr`), `⟦Φ⟧ = (p−1)(q−1) =
Φ(pq)` (`listToNat_subStr`, `DistinctPrimes.totient_mul`), the exponent word reads as
`e = sampleUnitL … .getD 1` (`unitSampleStr_eq`, `1 % Φ = 1` as `Φ ≥ 2`), `d` is the inverse
(`xgcdStr_pairEncode`), and each of `N, e, d < 2^{2M} − 1` is normalized to its `2M`-bit numeral
(`rsa_norm`). -/
private theorem rsa_genCore_spec (n : ℕ) (r : List Bool) :
    rsa_genCore (pairEncode (List.replicate (max n 2) true) r) = rsaGenOut n r := by
  have hy1 : pairFstD (pairEncode (List.replicate (max n 2) true) r) = List.replicate (max n 2) true :=
    pairFstD_pairEncode _ _
  have hy2 : pairSndD (pairEncode (List.replicate (max n 2) true) r) = r := pairSndD_pairEncode _ _
  have hP : rsa_gP (pairEncode (List.replicate (max n 2) true) r) =
      samplePrimeL (max n 2) (r.take (samplePrimeCoins.eval (max n 2))) := by
    rw [rsa_gP, hy1, hy2, List.length_replicate]
  have hQ : rsa_gQ (pairEncode (List.replicate (max n 2) true) r) =
      samplePrimeL (max n 2) ((r.drop (samplePrimeCoins.eval (max n 2))).take
        (samplePrimeCoins.eval (max n 2))) := by
    rw [rsa_gQ, hy1, hy2, List.length_replicate]
  have hones : listToNat (pairFstD (pairEncode (List.replicate (max n 2) true) r)) =
      2 ^ max n 2 - 1 := by
    rw [hy1, rsa_listToNat_ones]
  have hvalid : rsa_gValid (pairEncode (List.replicate (max n 2) true) r) =
      decide ((listToNat (samplePrimeL (max n 2) (r.take (samplePrimeCoins.eval (max n 2))))).Prime ∧
        (listToNat (samplePrimeL (max n 2) ((r.drop (samplePrimeCoins.eval (max n 2))).take
          (samplePrimeCoins.eval (max n 2))))).Prime ∧
        listToNat (samplePrimeL (max n 2) (r.take (samplePrimeCoins.eval (max n 2)))) ≠
          listToNat (samplePrimeL (max n 2) ((r.drop (samplePrimeCoins.eval (max n 2))).take
            (samplePrimeCoins.eval (max n 2)))) ∧
        listToNat (samplePrimeL (max n 2) (r.take (samplePrimeCoins.eval (max n 2)))) < 2 ^ max n 2 ∧
        listToNat (samplePrimeL (max n 2) ((r.drop (samplePrimeCoins.eval (max n 2))).take
          (samplePrimeCoins.eval (max n 2)))) < 2 ^ max n 2) := by
    rw [rsa_gValid, hP, hQ, hones]
    have h2 : 1 ≤ 2 ^ max n 2 := Nat.one_le_two_pow
    generalize listToNat (samplePrimeL (max n 2) (r.take (samplePrimeCoins.eval (max n 2)))) = a
    generalize listToNat (samplePrimeL (max n 2) ((r.drop (samplePrimeCoins.eval (max n 2))).take
      (samplePrimeCoins.eval (max n 2)))) = b
    generalize 2 ^ max n 2 = t at h2 ⊢
    rw [Bool.eq_iff_iff]
    by_cases ha : a.Prime <;> by_cases hb : b.Prime <;> simp only [ha, hb, decide_true,
      decide_false, Bool.true_and, Bool.false_and, true_and, false_and, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.false_eq_true]
    constructor
    · intro h
      omega
    · intro h
      omega
  have hzp : (rsaGenParams n r).z.p = listToNat (rsa_gPw (pairEncode (List.replicate (max n 2) true) r)) ∧
      (rsaGenParams n r).z.q = listToNat (rsa_gQw (pairEncode (List.replicate (max n 2) true) r)) := by
    rw [rsa_gPw, rsa_gQw, hvalid, hP, hQ]
    unfold rsaGenParams
    dsimp only
    split
    · next hc =>
      rw [if_pos (decide_eq_true hc), if_pos (decide_eq_true hc), DistinctPrimes.p_eq,
        DistinctPrimes.q_eq]
      exact ⟨rfl, rfl⟩
    · next hc =>
      rw [if_neg (fun h => hc (of_decide_eq_true h)), if_neg (fun h => hc (of_decide_eq_true h)),
        DistinctPrimes.default_p,
        DistinctPrimes.default_q, rsa_listToNat_two, rsa_listToNat_three]
      exact ⟨rfl, rfl⟩
  generalize hy : pairEncode (List.replicate (max n 2) true) r = y at hy1 hy2 hP hQ hones hvalid hzp
  -- the modulus, `Φ`, `e` and `d` read from the words
  have hN : listToNat (mulStr (pairEncode (rsa_gPw y) (rsa_gQw y))) = (rsaGenParams n r).N := by
    rw [rsa_listToNat_mulStr, ← hzp.1, ← hzp.2]
    rfl
  have hPhi : listToNat (rsa_gPhi y) =
      Nat.totient ((rsaGenParams n r).z.p * (rsaGenParams n r).z.q) := by
    rw [rsa_gPhi, rsa_listToNat_mulStr, listToNat_subStr, listToNat_subStr, rsa_listToNat_one,
      ← hzp.1, ← hzp.2, DistinctPrimes.totient_mul]
  have hΦ1 := (rsaGenParams n r).z.one_lt_totient
  have he : listToNat (rsa_gE y) = (rsaGenParams n r).e := by
    have hv := rsa_getD_spec (N := listToNat (rsa_gPhi y)) (by omega) (Nat.size (listToNat (rsa_gPhi y)))
      (rsaBlock.eval (pairFstD y).length) (rsaTrials.eval (pairFstD y).length)
      ((pairSndD y).drop ((PolyExpr.mul (.const 2) samplePrimeCoins).eval (pairFstD y).length))
    rw [rsa_gE, unitSampleStr_eq, listToNat_natToList (hv.1.trans (listToNat_lt_two_pow _)), hPhi,
      hy1, hy2, List.length_replicate, Nat.mod_eq_of_lt hΦ1, PolyExpr.eval_mul, PolyExpr.eval_const]
    rfl
  have hd : listToNat (pairSndD (xgcdStr (pairEncode (rsa_gE y) (rsa_gPhi y)))) =
      (rsaGenParams n r).d := by
    have hlt : (((rsaGenParams n r).e : ZMod (Nat.totient ((rsaGenParams n r).z.p *
        (rsaGenParams n r).z.q)))⁻¹).val < 2 ^ (rsa_gPhi y).length :=
      (ZMod.val_lt _).trans (hPhi ▸ listToNat_lt_two_pow _)
    rw [xgcdStr_pairEncode, pairSndD_pairEncode, he, hPhi, listToNat_natToList hlt]
    rfl
  -- the bound `N < 2^{2M} − 1`
  have hNb : (rsaGenParams n r).N < 2 ^ (2 * max n 2) - 1 := by
    have hp := (rsaGenParams n r).z.p_lt
    have hq := (rsaGenParams n r).z.q_lt
    have h4 : 4 ≤ 2 ^ max n 2 :=
      (Nat.pow_le_pow_right (by norm_num) (le_max_right n 2)).trans_eq' (by norm_num)
    have hsq : 2 ^ (2 * max n 2) = 2 ^ max n 2 * 2 ^ max n 2 := by rw [two_mul, pow_add]
    rw [hsq]
    show (rsaGenParams n r).z.p * (rsaGenParams n r).z.q < _
    obtain ⟨b, hb⟩ : ∃ b, 2 ^ max n 2 = b + 1 := ⟨2 ^ max n 2 - 1, by omega⟩
    rw [hb] at hp hq h4 ⊢
    have hpq := Nat.mul_le_mul (Nat.le_of_lt_succ hp) (Nat.le_of_lt_succ hq)
    have hexp : (b + 1) * (b + 1) = b * b + 2 * b + 1 := by ring
    rw [hexp]
    generalize (rsaGenParams n r).z.p * (rsaGenParams n r).z.q = x at hpq ⊢
    generalize b * b = w at hpq ⊢
    omega
  have hΦN : Nat.totient ((rsaGenParams n r).z.p * (rsaGenParams n r).z.q) ≤ (rsaGenParams n r).N :=
    Nat.totient_le _
  have hnorm : ∀ x, listToNat x < 2 ^ (2 * max n 2) - 1 →
      rsa_gNorm y x = natToList (2 * max n 2) (listToNat x) := by
    intro x hx
    rw [rsa_gNorm, hy1, List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_var, rsa_norm x _ hx]
  rw [rsa_genCore, hnorm _ (hN ▸ hNb), hnorm _ (he ▸ ((rsaGenParams n r).e_lt.trans_le hΦN).trans hNb),
    hnorm _ (hd ▸ ((rsaGenParams n r).d_lt.trans_le hΦN).trans hNb), hN, he, hd, rsaGenOut,
    rsaIndexOf, rsaTrapOf]

/-- **The generator is polynomial-time** [PS10, Theorem 53.2, "the set `I` is easy to
sample"] given the arithmetic bundle.

**Proof sketch.** First `1^m` with `m = max n 2`: `1^n` unless `n ≤ 1`, where it is `11`
(`polyTimeComputable_lenLe`, `polyTimeComputable_unaryPoly`, `polyTimeComputable_ite`); the rest
runs on `⟨1^m, r⟩`. Cut the coins at the unary lengths `1^{2m³}`
(`polyTimeComputable_pairTakePoly`/`_pairDropPoly samplePrimeCoins`); each prime is S1
(`polyTimeComputable_samplePrimeL` with `H.prime`); the validity test is two `H.prime` calls,
two `H.le` comparisons for `p ≠ q` and two `H.le` comparisons with `⟦1^m⟧ = 2^m − 1` for
`p, q < 2^m`, and the fallback words are the constants `⟦2⟧ = 10`, `⟦3⟧ = 11`
(`polyTimeComputable_ite`); `N` is `H.mul`; `Φ(N) = (p−1)(q−1)` by two decrements `H.sub` on
`⟨p, [true]⟩`, `⟨q, [true]⟩` (`listToNat_subStr`) and `H.mul`; `e` is
`polyTimeComputable_unitSampleStr` on the re-laid-out input `layout 1^m ⟦Φ⟧ [] (r.drop 4m³)`
(`NUPPT.polyTimeComputable_layout`; its fallback `1 % Φ = 1` as `Φ ≥ 2`); `d` is the second
component of `xgcdStr ⟨e, Φ⟩`; each of `N, e, d < 2^{2m} − 1` becomes its `2m`-bit numeral as the
remainder of `H.divMod` modulo the all-ones word `1^{2m}`; pair the numerals. -/
theorem polyTimeComputable_rsaGenRaw (H : ArithmeticFP) : PolyTimeComputable rsaGenRaw := by
  -- `1^{max n 2}`: `1^n` unless `n ≤ 1` (`polyTimeComputable_lenLe` against `[true]`)
  have hle : PolyTimeComputable fun z => [decide ((NUPPT.inParam z).length ≤ 1)] := by
    refine rsa_ptc_congr (rsa_comp polyTimeComputable_lenLe
      ((polyTimeComputable_const [true]).pairEncode NUPPT.polyTimeComputable_inParam)) fun z => ?_
    rw [pairFstD_pairEncode, pairSndD_pairEncode, List.length_singleton]
  have hun : PolyTimeComputable fun z => List.replicate (NUPPT.inParam z).length true := by
    refine rsa_ptc_congr (rsa_comp (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam)
      fun z => ?_
    rw [PolyExpr.eval_var]
  have hu := polyTimeComputable_ite (p := fun z => decide ((NUPPT.inParam z).length ≤ 1))
    (f := fun _ => [true, true]) (g := fun z => List.replicate (NUPPT.inParam z).length true)
    hle (polyTimeComputable_const _) hun
  have h := rsa_comp (rsa_genCore_poly H) (hu.pairEncode NUPPT.polyTimeComputable_inCoins)
  refine rsa_ptc_congr h fun z => ?_
  have hm : (if decide ((NUPPT.inParam z).length ≤ 1) then [true, true]
      else List.replicate (NUPPT.inParam z).length true) =
      List.replicate (max (NUPPT.inParam z).length 2) true := by
    by_cases h1 : (NUPPT.inParam z).length ≤ 1
    · rw [if_pos (decide_eq_true h1), max_eq_right (by omega)]
      rfl
    · rw [if_neg (by simpa using h1), max_eq_left (by omega)]
  rw [hm, rsa_genCore_spec, rsaGenRaw]

/-- **The RSA generator** `Gen(1^n) = ⟨⟨N, e⟩, ⟨N, d⟩⟩` as a uniform `NUPPT`
[PS10, Theorem 57.2, "`[(N, e), d] ← Gen(1^n)`"].

**Deviation (run-3 audit P3-5):** the trapdoor is `⟨N, d⟩` where the text's is `d`, because
`TrapdoorCollection.inv_spec` hands the inverter `⟨t, y⟩` without the index (the literal
`Inv((i, t), y)` form of Definition 56.1 (6) was not adopted); `N` is therefore carried in the
trapdoor. -/
noncomputable def rsaGen (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_rsaGenRaw H) rsaGenCoins

/-- The activation of the generator: `rsaGenOut n` on the coins. -/
theorem rsaGen_runAt (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n) :
    (rsaGen H).runAt n [] r = rsaGenOut n (List.ofFn r) := by
  rw [NUPPT.runAt_eq]
  unfold rsaGen
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rsaGenRaw, NUPPT.inParam_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq]

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, ⟨N, e⟩⟩, α⟩, r⟩`:
`unitSampleStr` on the modulus numeral. -/
def rsaSampleRaw (z : List Bool) : List Bool :=
  unitSampleStr (pairFstD (NUPPT.inArg z)) (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The unit sampler is polynomial-time** [PS10, Theorem 53.2, "the set `D_i` is also
easy to sample"]: for any polynomial-time projection `f` of the raw input to the modulus
numeral, `z ↦ unitSampleStr (f z) n (coins z)` is polynomial-time (shared by the RSA and
Rabin samplers).

**Proof sketch.** The unary bit length `1^{Nat.size N}` of `N = f z` is `H.size` (run-3
audit P7-1), and `1^{B(n)}`, `1^{T(n)}` are `polyTimeComputable_unaryPoly`. The trial loop
(`sampleUnitL = rejectBlocksL`) is the repetition host `polyTimeComputable_iterateFind` on the
state `⟨⟨1^{B(n)}, ⟨1^k, w⟩⟩, ⟨counter, coins⟩⟩` from `⟨⟨1^{B(n)}, ⟨1^k, w⟩⟩, ⟨1^{T(n)}, r⟩⟩`:
each step drops one counter token and one block of `B(n)` coins
(`polyTimeComputable_pairDropPoly var`), each trial reads the first `k` coins
(`polyTimeComputable_pairTakePoly var` on `⟨1^k, coins⟩`) and is accepted iff the counter is
nonempty, the value is below `N` (`H.le`), and the numeral of `gcd(v, N)` — which `xgcdStr`
returns at the width of `w` — reads `≤ 1` and `≥ 1` (two `H.le` tests against `[true]`); the
payload is the block behind a marker. The search over `|x| + 1 ≥ T(n)` rounds is the search of
`sampleUnitL` (the counter stops it at `T(n)`). The output is the remainder of
`H.divMod ⟨b, w⟩`, a numeral of the width of `w`, where `b` is the accepted block, or `[true]`
when no trial is accepted (`polyTimeComputable_isNil`, `polyTimeComputable_ite`): an accepted
`v < N` is its own remainder, and the fallback is `1 mod N`. -/
theorem polyTimeComputable_unitSampleStr (H : ArithmeticFP) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
  exact rsa_ptc_unitSampleStr H hf

/-- The domain sampler of the RSA collection is polynomial-time. -/
theorem polyTimeComputable_rsaSampleRaw (H : ArithmeticFP) : PolyTimeComputable rsaSampleRaw :=
  polyTimeComputable_unitSampleStr H (polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg)

/-- **The domain sampler of the RSA collection**: a uniform `NUPPT` with `T(n) B(n)` coins. -/
noncomputable def rsaSampler (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_rsaSampleRaw H) rsaSampleCoins

/-- The string function of the trapdoor inverter on the raw layout `⟨⟨⟨1^n, ⟨⟨N, d⟩, y⟩⟩, α⟩, r⟩`:
`y^d mod N` by one modular exponentiation [PS10, Theorem 57.2, `f⁻¹_{N,d}(y) = y^d mod N`]. -/
def rsaInvRaw (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (NUPPT.inArg z))
    (pairEncode (pairSndD (pairFstD (NUPPT.inArg z))) (pairFstD (pairFstD (NUPPT.inArg z)))))

/-- The inverter's string function is polynomial-time given modular exponentiation. -/
theorem polyTimeComputable_rsaInvRaw (H : ArithmeticFP) : PolyTimeComputable rsaInvRaw :=
  H.modExp.comp ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
    ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp
      NUPPT.polyTimeComputable_inArg)).pairEncode
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
        NUPPT.polyTimeComputable_inArg))))

/-- **The trapdoor inverter** `Inv(1^n, ⟨⟨N, d⟩, y⟩) = y^d mod N` as a uniform `NUPPT` without
coins. -/
noncomputable def rsaInv (H : ArithmeticFP) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_rsaInvRaw H) (.const 0)

/-- The activation of the inverter on `⟨⟨N, d⟩, y⟩`. -/
theorem rsaInv_runAt (H : ArithmeticFP) (n : ℕ) (t y : List Bool) (s : (rsaInv H).Coins n) :
    (rsaInv H).runAt n (pairEncode t y) s =
      natToList (pairFstD t).length (listToNat y ^ listToNat (pairSndD t) % listToNat (pairFstD t)) := by
  rw [NUPPT.runAt_eq]
  unfold rsaInv
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp [rsaInvRaw, NUPPT.inArg_eq, NUPPT.advInput_eq]

/-- **The trapdoor inverter decodes to `f⁻¹_{N,e}(y) = y^d`** at every generated index
(the clause `inv_spec` of `TrapdoorCollection`, [PS10, Theorem 57.2, "`e·d = 1 mod Φ(N)`"]).

**Proof sketch.** By `rsaGen_runAt` the index is `⟨N, e⟩` and the trapdoor `⟨N, d⟩` of
`P := rsaGenParams`; the index is valid (`rsaValid_indexOf`, `rsaMod_indexOf`), so
`rsaEnc i y` is the numeral of `y.val`; `rsaInv_runAt` returns the numeral of
`y.val^d mod N = (y^d).val` (`val_units_pow`), which `rsaDec` decodes to `y^d`
(`rsaDec_rsaEnc`); and `(rsaPermAt i).symm y = y^d` by `rsaPerm_symm_apply` with `P.ed`. -/
theorem rsaInv_spec (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n)
    (y : (ZMod (rsaMod (pairFstD ((rsaGen H).runAt n [] r))))ˣ) (s : (rsaInv H).Coins n) :
    rsaDec _ ((rsaInv H).runAt n (pairEncode (pairSndD ((rsaGen H).runAt n [] r)) (rsaEnc _ y)) s) =
      some ((rsaPermAt _).symm y) := by
  revert y
  rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode, pairSndD_pairEncode]
  generalize rsaGenParams n (List.ofFn r) = P
  intro y
  have hv := rsaValid_indexOf _ P
  have hM := rsaMod_indexOf _ P
  have hlen : (pairFstD (rsaIndexOf _ P)).length = 2 * max n 2 := by
    simp [rsaIndexOf]
  have hed : rsaE (rsaIndexOf _ P) * P.d ≡ 1 [MOD Nat.totient (rsaMod (rsaIndexOf _ P))] := by
    rw [hM, rsaE_indexOf]; exact P.ed
  have hsymm : (rsaPermAt (rsaIndexOf _ P)).symm y = y ^ P.d := by
    unfold rsaPermAt
    rw [dif_pos hv]
    exact rsaPerm_symm_apply _ _ _ _ hed y
  have henc : listToNat (rsaEnc (rsaIndexOf _ P) y) = (y : ZMod (rsaMod (rsaIndexOf _ P))).val := by
    unfold rsaEnc rsaEncVal
    rw [if_pos hv]
    exact listToNat_natToList (val_lt_two_pow _ y)
  rw [rsaInv_runAt, hsymm]
  simp only [rsaTrapOf, pairFstD_pairEncode, pairSndD_pairEncode, length_natToList,
    listToNat_natToList P.N_lt, listToNat_natToList P.d_lt_two_pow, henc]
  have hval : (y : ZMod (rsaMod (rsaIndexOf _ P))).val ^ P.d % P.N =
      ((y ^ P.d : (ZMod (rsaMod (rsaIndexOf _ P)))ˣ) : ZMod (rsaMod (rsaIndexOf _ P))).val := by
    rw [val_units_pow]
    exact congrArg (fun M => (y : ZMod (rsaMod (rsaIndexOf _ P))).val ^ P.d % M) hM.symm
  rw [hval, ← rsaDec_rsaEnc (rsaIndexOf _ P) (y ^ P.d)]
  congr 1
  unfold rsaEnc rsaEncVal
  rw [if_pos hv, hlen]

/-- The activation of the domain sampler: `rsaSampler` on the index `i` is `unitSampleStr` on
the modulus numeral `pairFstD i` (`NUPPT.runAtL_ofPolyTimeUniform` and the layout equations). -/
private theorem rsa_sampler_runAt (H : ArithmeticFP) (n : ℕ) (i : List Bool)
    (s : (rsaSampler H).Coins n) :
    (rsaSampler H).runAt n i s = unitSampleStr (pairFstD i) n (List.ofFn s) := by
  rw [NUPPT.runAt_eq]
  unfold rsaSampler
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [rsaSampleRaw, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- At a generated index `⟨N, e⟩` the sampler's string decodes: `rsaDec` accepts
`unitSampleStr` of the modulus numeral (it is the `2m`-bit numeral of a unit `v < N`,
`rsa_getD_spec`). -/
private theorem rsa_dec_unitSampleStr {m : ℕ} (P : RSAParams m) (n : ℕ) (r : List Bool) :
    ∃ x, rsaDec (rsaIndexOf m P) (unitSampleStr (pairFstD (rsaIndexOf m P)) n r) = some x := by
  have hw : pairFstD (rsaIndexOf m P) = natToList (2 * m) P.N := by
    rw [rsaIndexOf, pairFstD_pairEncode]
  have hN : listToNat (natToList (2 * m) P.N) = P.N := listToNat_natToList P.N_lt
  have hpos : 0 < P.N := NeZero.pos (P.z.p * P.z.q)
  have hv := rsa_getD_spec hpos (Nat.size P.N) (rsaBlock.eval n) (rsaTrials.eval n) r
  set v := (sampleUnitL P.N (Nat.size P.N) (rsaBlock.eval n) (rsaTrials.eval n) r).getD (1 % P.N)
  have hval : listToNat (natToList (2 * m) v) = v := listToNat_natToList (hv.1.trans P.N_lt)
  have hM := rsaMod_indexOf m P
  rw [unitSampleStr_eq, hw, hN, length_natToList, rsaDec, if_pos (rsaValid_indexOf m P)]
  rw [dif_pos ⟨by rw [length_natToList, hw, length_natToList], by rw [hval, hM]; exact hv.1,
    by rw [hval, hM]; exact hv.2⟩]
  exact ⟨_, rfl⟩

/-- **The RSA sampler's outputs decode and evaluate honestly** (the clause `sample_spec` of
`Collection`, [PS10, Definition 41.1 (2)]; repair of the run-3 audit, P3-1): at every parameter
the generated index `⟨N, e⟩` is valid with modulus `N` (`rsaGen_runAt`, `rsaValid_indexOf`,
`rsaMod_indexOf`), and the sampler outputs the `2m`-bit numeral of a unit `v < N`
(`sampleUnitL_spec`, or the fallback `1 % N = 1`), which `rsaDec` decodes to
`x = ZMod.unitOfCoprime v` with `rsaEnc i x` the same numeral; `rsaEval_spec` gives the
evaluator clause.

**Proof sketch.** Unfold the activation (`NUPPT.runAtL_ofPolyTimeUniform`, `rsaSampleRaw`,
`unitSampleStr`, `rsaGen_runAt`), case on `sampleUnitL`; `rsaDec`'s test is discharged by
`length_natToList`, `listToNat_natToList` (`v < N < 2^{2m}`), `sampleUnitL_spec` resp.
`Nat.coprime_one_left`; the decoded unit has value `v` (`ZMod.coe_unitOfCoprime`,
`ZMod.val_natCast`, `Nat.mod_eq_of_lt`), so `rsaEnc i x = natToList (2m) v` and
`rsaEval_spec` applies. -/
theorem rsaSampler_spec (H : ArithmeticFP) (n : ℕ) (r : (rsaGen H).Coins n)
    (s : (rsaSampler H).Coins n) :
    ∃ x, rsaDec (pairFstD ((rsaGen H).runAt n [] r))
        ((rsaSampler H).runAt n (pairFstD ((rsaGen H).runAt n [] r)) s) = some x ∧
      rsaEval (pairEncode (pairFstD ((rsaGen H).runAt n [] r))
        ((rsaSampler H).runAt n (pairFstD ((rsaGen H).runAt n [] r)) s)) = rsaF _ x := by
  rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode, rsa_sampler_runAt]
  generalize rsaGenParams n (List.ofFn r) = P
  obtain ⟨x, hx⟩ := rsa_dec_unitSampleStr P n (List.ofFn s)
  refine ⟨x, hx, ?_⟩
  rw [← rsaEnc_of_rsaDec hx, rsaEval_spec]

/-! ## The RSA trapdoor collection [PS10, Theorems 53.2 and 57.2] -/

/-- **The RSA collection of trapdoor permutations** [PS10, Theorem 57.2; Theorem 53.2 for
the underlying collection]: indices `⟨N, e⟩`, domains `D_{⟨N,e⟩} = Z_N^*` (valid indices),
`f_{N,e}(x) = x^e mod N`, the generator `rsaGen`, the sampler `rsaSampler`, the evaluator
`rsaEval` (one modular exponentiation), the permutation `x ↦ x^e` [PS10, Theorem 54.3] and
the inverter `rsaInv` computing `y^d mod N` from the trapdoor `⟨N, d⟩`.

**Deviation:** module docstring (valid/invalid indices, trapdoor `⟨N, d⟩`, truncated
samplers, `max n 2`). -/
noncomputable def rsaTrapdoor (H : ArithmeticFP) : TrapdoorCollection where
  D i := (ZMod (rsaMod i))ˣ
  encD := rsaEnc
  decD := rsaDec
  decD_encD := rsaDec_rsaEnc
  encD_decD _ _ _ := rsaEnc_of_rsaDec
  f := rsaF
  gen := rsaGen H
  gen_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  sample := rsaSampler H
  sample_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  eval := rsaEval
  eval_poly := polyTimeComputable_rsaEval H
  eval_spec := rsaEval_spec
  sample_spec := rsaSampler_spec H
  perm := rsaPermAt
  f_perm := rsaF_perm
  inv := rsaInv H
  inv_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  inv_spec := rsaInv_spec H

/-- **The domain of the RSA trapdoor collection is `Z_N^*`**: the published equivalence
`(rsaTrapdoor H).D i ≃ (ZMod (rsaMod i))ˣ` (the identity). It is the interface to the domain:
elements of `D i` are read through it (`rsaTrapdoor_f`, `rsaTrapdoor_encD`, `rsaTrapdoor_decD`,
`rsaTrapdoor_perm`), so no statement needs the collection to reduce at the type level, and
uniform statements over `D i` transport along it (`uprob_comp_equiv`,
`StatClose.comp_equiv_right`). -/
def rsaTrapdoor_domEquiv (H : ArithmeticFP) (i : List Bool) :
    (rsaTrapdoor H).D i ≃ (ZMod (rsaMod i))ˣ :=
  Equiv.refl _

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_N^*`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = rsaTrapdoor_domEquiv H i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem rsaTrapdoor_domEquiv_uprob (H : ArithmeticFP) (i : List Bool)
    (P : (ZMod (rsaMod i))ˣ → Prop) :
    uprob (fun x : (rsaTrapdoor H).D i => P (rsaTrapdoor_domEquiv H i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of the RSA trapdoor collection is `rsaF`, read through the domain equivalence:
`(rsaTrapdoor H).f i x = rsaF i (rsaTrapdoor_domEquiv H i x)`. -/
theorem rsaTrapdoor_f (H : ArithmeticFP) (i : List Bool) (x : (rsaTrapdoor H).D i) :
    (rsaTrapdoor H).f i x = rsaF i (rsaTrapdoor_domEquiv H i x) := rfl

/-- The encoder of the RSA trapdoor collection is `rsaEnc`, read through the domain
equivalence: `(rsaTrapdoor H).encD i x = rsaEnc i (rsaTrapdoor_domEquiv H i x)`. -/
theorem rsaTrapdoor_encD (H : ArithmeticFP) (i : List Bool) (x : (rsaTrapdoor H).D i) :
    (rsaTrapdoor H).encD i x = rsaEnc i (rsaTrapdoor_domEquiv H i x) := rfl

/-- The decoder of the RSA trapdoor collection is `rsaDec`, carried back along the domain
equivalence: `(rsaTrapdoor H).decD i w = (rsaDec i w).map (rsaTrapdoor_domEquiv H i).symm`. -/
theorem rsaTrapdoor_decD (H : ArithmeticFP) (i w : List Bool) :
    (rsaTrapdoor H).decD i w = (rsaDec i w).map (rsaTrapdoor_domEquiv H i).symm := by
  show rsaDec i w = _
  cases rsaDec i w <;> rfl

/-- The permutation of the RSA trapdoor collection is `rsaPermAt` (`x ↦ x^e`), read through the
domain equivalence: with `φ = rsaTrapdoor_domEquiv H i`,
`(rsaTrapdoor H).perm i x = φ.symm (rsaPermAt i (φ x))`. -/
theorem rsaTrapdoor_perm (H : ArithmeticFP) (i : List Bool) (x : (rsaTrapdoor H).D i) :
    (rsaTrapdoor H).perm i x =
      (rsaTrapdoor_domEquiv H i).symm (rsaPermAt i (rsaTrapdoor_domEquiv H i x)) := rfl

/-- The index generator of the RSA trapdoor collection is `rsaGen H`. -/
theorem rsaTrapdoor_gen (H : ArithmeticFP) : (rsaTrapdoor H).gen = rsaGen H := rfl

/-- The domain sampler of the RSA trapdoor collection is `rsaSampler H`. -/
theorem rsaTrapdoor_sample (H : ArithmeticFP) : (rsaTrapdoor H).sample = rsaSampler H := rfl

/-- The evaluator of the RSA trapdoor collection is `rsaEval`. -/
theorem rsaTrapdoor_eval (H : ArithmeticFP) : (rsaTrapdoor H).eval = rsaEval := rfl

/-- The trapdoor inverter of the RSA trapdoor collection is `rsaInv H`. -/
theorem rsaTrapdoor_inv (H : ArithmeticFP) : (rsaTrapdoor H).inv = rsaInv H := rfl

/-- **The RSA collection** [PS10, Theorem 53.2]: the collection underlying `rsaTrapdoor`. -/
noncomputable def rsaCollection (H : ArithmeticFP) : Collection := (rsaTrapdoor H).toCollection

/-- **The domain of the RSA collection is `Z_N^*`**: the published equivalence
`(rsaCollection H).D i ≃ (ZMod (rsaMod i))ˣ`, that of the underlying trapdoor collection
(`rsaTrapdoor_domEquiv`); the interface to the domain (`rsaCollection_f`,
`rsaCollection_encD`, `rsaCollection_decD`). -/
def rsaCollection_domEquiv (H : ArithmeticFP) (i : List Bool) :
    (rsaCollection H).D i ≃ (ZMod (rsaMod i))ˣ :=
  rsaTrapdoor_domEquiv H i

/-- **The domain equivalence carries the uniform distribution**: for `P` on `Z_N^*`,
`Pr_{x ← D i}[P (φ x)] = Pr_y[P y]` with `φ = rsaCollection_domEquiv H i` (`uprob_comp_equiv`),
the form in which uniform statements over the domain are read. -/
theorem rsaCollection_domEquiv_uprob (H : ArithmeticFP) (i : List Bool)
    (P : (ZMod (rsaMod i))ˣ → Prop) :
    uprob (fun x : (rsaCollection H).D i => P (rsaCollection_domEquiv H i x)) = uprob P :=
  uprob_comp_equiv _ P

/-- The function of the RSA collection is `rsaF`, read through the domain equivalence:
`(rsaCollection H).f i x = rsaF i (rsaCollection_domEquiv H i x)`. -/
theorem rsaCollection_f (H : ArithmeticFP) (i : List Bool) (x : (rsaCollection H).D i) :
    (rsaCollection H).f i x = rsaF i (rsaCollection_domEquiv H i x) := rsaTrapdoor_f H i x

/-- The encoder of the RSA collection is `rsaEnc`, read through the domain equivalence:
`(rsaCollection H).encD i x = rsaEnc i (rsaCollection_domEquiv H i x)`. -/
theorem rsaCollection_encD (H : ArithmeticFP) (i : List Bool) (x : (rsaCollection H).D i) :
    (rsaCollection H).encD i x = rsaEnc i (rsaCollection_domEquiv H i x) := rsaTrapdoor_encD H i x

/-- The decoder of the RSA collection is `rsaDec`, carried back along the domain equivalence:
`(rsaCollection H).decD i w = (rsaDec i w).map (rsaCollection_domEquiv H i).symm`. -/
theorem rsaCollection_decD (H : ArithmeticFP) (i w : List Bool) :
    (rsaCollection H).decD i w = (rsaDec i w).map (rsaCollection_domEquiv H i).symm :=
  rsaTrapdoor_decD H i w

/-- The index generator of the RSA collection is `rsaGen H`. -/
theorem rsaCollection_gen (H : ArithmeticFP) : (rsaCollection H).gen = rsaGen H := rfl

/-- The domain sampler of the RSA collection is `rsaSampler H`. -/
theorem rsaCollection_sample (H : ArithmeticFP) : (rsaCollection H).sample = rsaSampler H := rfl

/-- The evaluator of the RSA collection is `rsaEval`. -/
theorem rsaCollection_eval (H : ArithmeticFP) : (rsaCollection H).eval = rsaEval := rfl

/-- The index generated by the RSA collection is `⟨N, e⟩` of `rsaGenParams`. -/
theorem rsaCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rsaCollection H).gen.Coins n) :
    (rsaCollection H).index n r = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
  have key : ∀ (g : NUPPT), g = rsaGen H → ∀ r : g.Coins n,
      pairFstD (g.runAt n [] r) = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
    rintro g rfl r
    rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode]
  rw [Collection.index_eq]
  exact key _ (rsaCollection_gen H) r

/-- The statistical error of the honest samplers at parameter `n`:
`2 · 2^{-n}` (two `SamplePrime` failures), `2n/2^n` (the diagonal `p = q`) and `e^{-n}`
(the unit sampler), negligible. -/
noncomputable def rsaGenErr (n : ℕ) : ℝ := 2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n + Real.exp (-(n : ℝ))

/-- `rsaGenErr` is negligible.

**Proof sketch.** `negligible_two_pow_neg` with `Negligible.const_mul`, `Negligible.mul_pow`
(`2n/2^n = 2 · n · (1/2)^n`) and `Negligible.mono` with `exp_neg_le_half_pow`;
`Negligible.add`. -/
theorem negligible_rsaGenErr : Negligible rsaGenErr := by
  have h1 : Negligible fun n : ℕ => (1 / 2 : ℝ) ^ n := by
    simpa [one_div] using negligible_two_pow_neg
  have h4 : Negligible fun n : ℕ => Real.exp (-(n : ℝ)) :=
    h1.mono ⟨0, fun n _ => by
      rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
      exact exp_neg_le_half_pow n⟩
  refine (((h1.const_mul 2).add ((h1.mul_pow 1).const_mul 2)).add h4).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  unfold rsaGenErr
  rw [pow_one, one_div, inv_pow]
  field_simp

/-- The domain sampler has `T(n) B(n)` coins: `(rsaSampler H).coins = rsaSampleCoins`. -/
private theorem rsa_coins_sampler (H : ArithmeticFP) : (rsaSampler H).coins = rsaSampleCoins := by
  unfold rsaSampler
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- The modulus of generated parameters fits the blocks: `Nat.size N ≤ b` whenever `2m ≤ b`
(`N < 2^{2m}`, `Nat.size_le`). -/
private theorem rsa_size_N_le {m : ℕ} (P : RSAParams m) {b : ℕ} (hb : 2 * m ≤ b) :
    Nat.size P.N ≤ b :=
  (Nat.size_le.2 P.N_lt).trans hb

/-- **The decoded unit sampler at a generated index is close to uniform**: at the index
`i = ⟨N, e⟩` of `P`, `rsaDec i (unitSampleStr ⟦N⟧ n r)` on uniform coins `r` is within `e^{-n}`
of the uniform unit of `Z_N`, given `Nat.size N ≤ B(n)`.

**Proof sketch.** The sampler string is the `2m`-bit numeral of the S3 sampler's value at the
modulus `rsaMod i = N` (`unitSampleStr_eq`, `listToNat_natToList`, `rsaMod_indexOf`), and the
numeral of `x.val` is `rsaEnc i x` (valid index), which `rsaDec` decodes to `x`
(`rsaDec_rsaEnc`). So both samplers are the images under `v ↦ rsaDec i ⟦v⟧_{2m}` of the two
samplers of `statClose_sampleUnitL` (at `N = rsaMod i`), and `StatClose.map` concludes. -/
private theorem rsa_statClose_dec {m : ℕ} (P : RSAParams m) (n : ℕ)
    (hk : Nat.size P.N ≤ rsaBlock.eval n) :
    StatClose (fun s : Fin (rsaSampleCoins.eval n) → Bool =>
        rsaDec (rsaIndexOf m P) (unitSampleStr (pairFstD (rsaIndexOf m P)) n (List.ofFn s)))
      (fun x : (ZMod (rsaMod (rsaIndexOf m P)))ˣ => some x) (Real.exp (-(n : ℝ))) := by
  have hw : pairFstD (rsaIndexOf m P) = natToList (2 * m) P.N := by
    rw [rsaIndexOf, pairFstD_pairEncode]
  have hN : listToNat (natToList (2 * m) P.N) = P.N := listToNat_natToList P.N_lt
  have hM := rsaMod_indexOf m P
  have hv := rsaValid_indexOf m P
  have hS := (statClose_sampleUnitL n (rsaMod (rsaIndexOf m P)) (by rw [hM]; exact hk)).map
    (fun v => rsaDec (rsaIndexOf m P) (natToList (2 * m) v))
  have eX : (fun s : Fin (rsaSampleCoins.eval n) → Bool => rsaDec (rsaIndexOf m P)
      (natToList (2 * m) ((sampleUnitL (rsaMod (rsaIndexOf m P)) (Nat.size (rsaMod (rsaIndexOf m P)))
        (rsaBlock.eval n) (rsaTrials.eval n) (List.ofFn s)).getD (1 % rsaMod (rsaIndexOf m P))))) =
      fun s => rsaDec (rsaIndexOf m P) (unitSampleStr (pairFstD (rsaIndexOf m P)) n (List.ofFn s)) := by
    funext s
    rw [unitSampleStr_eq, hw, hN, length_natToList]
    congr 2
    rw [hM]
  have eY : (fun x : (ZMod (rsaMod (rsaIndexOf m P)))ˣ => rsaDec (rsaIndexOf m P)
      (natToList (2 * m) (x : ZMod (rsaMod (rsaIndexOf m P))).val)) = fun x => some x := by
    funext x
    have hx : natToList (2 * m) (x : ZMod (rsaMod (rsaIndexOf m P))).val = rsaEnc (rsaIndexOf m P) x := by
      rw [rsaEnc, rsaEncVal, if_pos hv, hw, length_natToList]
    rw [hx, rsaDec_rsaEnc]
  rw [eX, eY] at hS
  exact hS

/-- **The domain sampler is close to uniform** [PS10, Theorem 53.2, "the set `D_i` is also
easy to sample"]: the decoded output of `rsaSampler` at a generated index is within a
negligible statistical distance of the uniform element of `Z_N^*`.

**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := e^{-n}` for `n ≥ 2`. At a generated
index `⟨N, e⟩` (`rsaCollection_index`, valid by `rsaValid_indexOf`, `N = pq < 2^{2n}`) the
sampler's output is `unitSampleStr` on the numeral of `N` (`NUPPT.runAtL_ofPolyTimeUniform`,
`rsaSampleRaw`): `T(n)` trials each reading `k = Nat.size N ≤ 2n` uniform bits
(`k ≤ B(n)`), accepted iff the value is a unit; `sampleUnitL` is `rejectBlocksL` of the unit
predicate, so `statClose_rejectBlocksL` (default `1`) gives closeness `(1 - Pr[unit])^{T(n)}`
to the uniform element of `{v < 2^k | v < N ∧ gcd(v, N) = 1} ≃ Z_N^*`, decoded by `rsaDec` to
the uniform element of `Z_N^*` (`StatClose.map`, `decodeFin`-style injectivity). The acceptance rate is `Φ(N)/2^k ≥ Φ(N)/(2N) ≥ 1/(2k)`
(`Nat.lt_size_self`, `Nat.size_le`, `NumberTheory.le_totient_mul_log_succ`) `≥ 1/(4n+8)`,
and `(1 - 1/(4n+8))^{(4n+8)n} ≤ e^{-n}` (`one_sub_one_div_pow_le_exp_neg`). Negligibility:
`exp_neg_le_half_pow`, `negligible_two_pow_neg`, `Negligible.mono`. -/
theorem rsaCollection_sampleClose (H : ArithmeticFP) :
    ∃ δ : ℕ → ℝ, Negligible δ ∧ (rsaCollection H).SampleClose δ := by
  refine ⟨fun n => if n < 2 then 1 else Real.exp (-(n : ℝ)), ?_, ?_⟩
  · have h1 : Negligible fun n : ℕ => (1 / 2 : ℝ) ^ n := by
      simpa [one_div] using negligible_two_pow_neg
    have h4 : Negligible fun n : ℕ => Real.exp (-(n : ℝ)) :=
      h1.mono ⟨0, fun n _ => by
        rw [abs_of_pos (Real.exp_pos _), abs_of_pos (by positivity)]
        exact exp_neg_le_half_pow n⟩
    exact h4.mono ⟨2, fun n hn => by rw [if_neg (by omega)]⟩
  rw [Collection.sampleClose_iff]
  intro n r
  have hδ : Real.exp (-(n : ℝ)) ≤ if n < 2 then 1 else Real.exp (-(n : ℝ)) := by
    split_ifs
    · exact Real.exp_le_one_iff.2 (by simp)
    · exact le_rfl
  refine StatClose.mono ?_ hδ
  rw [rsaCollection_index, rsaCollection_sample]
  simp only [rsaCollection_decD, rsa_sampler_runAt]
  have hk : Nat.size (rsaGenParams n (List.ofFn r)).N ≤ rsaBlock.eval n :=
    rsa_size_N_le _ (by rw [eval_rsaBlock]; omega)
  have h1 := ((rsa_statClose_dec (rsaGenParams n (List.ofFn r)) n hk).map
    (Option.map (rsaCollection_domEquiv H _).symm)).comp_equiv_left
      (NUPPT.coinsEquivPoly (rsa_coins_sampler H) n) |>.comp_equiv_right
      (rsaCollection_domEquiv H _)
  simp only [NUPPT.coinsEquivPoly_ofFn, Option.map_some, Equiv.symm_apply_apply] at h1
  exact h1

/-- **The RSA adversary of an inverter of the collection** [PS10, proof of Theorem 53.2]:
`A'(1^n, ⟨N, ⟨e, y⟩⟩) := A(1^n, ⟨⟨N, e⟩, y⟩)`, a re-pairing of the input; coins and advice
of `A`. -/
noncomputable def rsaBreaker (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime
    (f := fun z => A.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairEncode (pairFstD (NUPPT.inArg z)) (pairFstD (pairSndD (NUPPT.inArg z))))
        (pairSndD (pairSndD (NUPPT.inArg z))))
      (NUPPT.inAdvice z) (NUPPT.inCoins z)))
    (A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam
      (((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
          NUPPT.polyTimeComputable_inArg))).pairEncode
        (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
          NUPPT.polyTimeComputable_inArg)))
      NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins))
    A.coins A.adv A.advice A.advice_length

/-- `rsaBreaker` has the coins of `A`. -/
@[simp] theorem coins_rsaBreaker (A : NUPPT) : (rsaBreaker A).coins = A.coins := by
  unfold rsaBreaker
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **`rsaBreaker` runs on the coins of `A`**: the published equivalence
`(rsaBreaker A).Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along `coins_rsaBreaker`). -/
noncomputable def rsaBreaker_coinsEquiv (A : NUPPT) (n : ℕ) : (rsaBreaker A).Coins n ≃ A.Coins n :=
  NUPPT.coinsCongr (coins_rsaBreaker A) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (rsaBreaker_coinsEquiv A n r) = List.ofFn r`. -/
theorem rsaBreaker_coinsEquiv_ofFn (A : NUPPT) (n : ℕ)
    (r : (rsaBreaker A).Coins n) :
    List.ofFn (rsaBreaker_coinsEquiv A n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn (coins_rsaBreaker A) n r

/-- The activation of `rsaBreaker`: `A'(1^n, ⟨N, ⟨e, y⟩⟩; r) = A(1^n, ⟨⟨N, e⟩, y⟩; φ r)`, the
coins read through `φ = rsaBreaker_coinsEquiv A n`. -/
theorem rsaBreaker_runAt (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaBreaker A).Coins n) :
    (rsaBreaker A).runAt n (pairEncode N (pairEncode e y)) r =
      A.runAt n (pairEncode (pairEncode N e) y) (rsaBreaker_coinsEquiv A n r) := by
  rw [NUPPT.runAt_eq, rsaBreaker_coinsEquiv, NUPPT.runAt_coinsCongr]
  unfold rsaBreaker
  rw [NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.runAtL_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
    NUPPT.inAdvice_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode]

/-- **Inverting the RSA collection breaks the RSA assumption** [PS10, proof of Theorem 53.2]:
for `n ≥ 2`, the inversion probability of `A` against the RSA collection is at most the RSA
probability of `rsaBreaker A` plus the statistical error of the generator.

**Proof sketch.** At a generated index `⟨N, e⟩` (`rsaCollection_index`, valid), the domain
is `Z_N^*` (`rsaMod_indexOf`), `f_{N,e}(x)` is the numeral of `(x^e).val` (`rsaF_perm`,
`rsaEnc`), and a decoded answer `x'` with `f x' = f x` has `x' = x` (`PermCollection.f_injective`),
so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", which implies the RSA
event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`,
`rsaBreaker_coinsEquiv`, `decodeFin_ofFn`, `bitsToNat_natToBits`, `val_units_pow`). Since
`x ↦ x^e` pushes uniform to uniform (`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the
inner probability equals the RSA inner probability at `(z, e)`: a number `h(z, e) ∈ [0, 1]`
(over `y` and `A`'s coins).
The exponent group `Z*_{Φ(N)}` depends on `z`, so the generator's law is not compared with one
uniform product: the comparison is a conditional expectation over `z`. Split the generator's
coins into the two prime segments and the exponent segment (`rsaGenParams`, `uexp_prod`,
`uprob_prod`). (i) For each fixed prime pair `z`, the exponent drawn from the exponent segment
(`sampleUnitL` modulo `Φ(N)`, fallback `1`) is within `e^{-n}` of the uniform element of
`Z*_{Φ(N)}` (`statClose_rejectBlocksL` with the acceptance rate of the sampleClose sketch), so
the conditional success at `z` exceeds `g(z) := E_{e uniform}[h(z, e)]` by at most `e^{-n}`
(`StatClose.abs_uprob_sub_le_prod`, with `(y, r)` as the auxiliary coins). (ii) The law of `z`
under the two prime segments is within `2 · 2^{-n} + 2n/2^n` of the uniform law on
`DistinctPrimes n` (`statClose_samplePrime` with the prime fallback `natToBits n 2` of
`samplePrimeL` — run-3 audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map`
through the validity test with `uprob_diag` and `one_div_card_primes_le` for the fallback on
`p = q`); averaging the `[0, 1]`-valued `g` over that law instead of the uniform one costs at
most that distance (`StatClose.abs_uprob_sub_le_prod` again, with `g(z)` read as a probability
over the auxiliary coins `ω : Π z', Z*_{Φ(N')} × Z_{N'}^* × A.Coins n` at `ω z`). (iii) Adding
the conditional exponent error, the inversion probability is at most
`uexp g + (2 · 2^{-n} + 2n/2^n) + e^{-n} = rsaProb (rsaBreaker A) n + rsaGenErr n`, as
`rsaProb` is the outer `uexp` over `z` of the inner probability over `(e, y, r)`. No error
beyond `rsaGenErr n` is needed. -/
theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
  sorry

/-- **Theorem 53.2** [PS10, Theorem 53.2]: under the RSA assumption (and the arithmetic
hypotheses), the RSA collection `{f_{N,e}(x) = x^e mod N}` is a collection of one-way
functions.

**Deviation:** module docstring (distinct primes, truncated samplers, valid indices).

**Proof sketch.** The sampling clause is `rsaCollection_sampleClose H`. For the hardness
clause fix `A`: `rsaCollection_invProbAt_le H A` bounds the inversion probability by
`rsaProb (rsaBreaker A) n + rsaGenErr n` for `n ≥ 2`, negligible by `hR (rsaBreaker A)`,
`negligible_rsaGenErr` and `Negligible.add`; conclude by `Negligible.mono`
(`Collection.invProbAt_nonneg`, threshold `2`). -/
theorem rsaCollection_oneWay (H : ArithmeticFP) (hR : RSAAssumption) : (rsaCollection H).OneWay := by
  sorry

/-- **Theorem 57.2** [PS10, Theorem 57.2]: under the RSA assumption (and the arithmetic
hypotheses), RSA with `Gen(1^n) = ((N, e), d)` and `f⁻¹_{N,d}(y) = y^d mod N` is a collection
of trapdoor permutations: clauses (1)–(4) and (6) are the data of `rsaTrapdoor`
(`rsaPermAt` [Theorem 54.3], `rsaGen`, `rsaSampler`, `rsaEval`, `rsaInv_spec`), and the
hardness clause (5) is `rsaCollection_oneWay`. -/
theorem rsaTrapdoor_oneWay (H : ArithmeticFP) (hR : RSAAssumption) : (rsaTrapdoor H).OneWay :=
  rsaCollection_oneWay H hR

/-! ## RSA implies factoring [PS10, Theorem 55.2, Algorithm 55.3] -/

/-- **The computation of `A'`** [PS10, Algorithm 55.3] after the call `p' ← A(N)`: `q' := N / p'`;
abort (output `[]`) unless `p' q' = N`; `Φ := (p'−1)(q'−1)`; `d := e⁻¹ mod Φ`
(`ExtendedEuclid`, `ZMod.inv`); output `y^d mod N` as a `2n`-bit numeral.

**Deviation:** the factoring adversary of Assumption 30.1 returns one factor; the other is
recovered by division (text issue). -/
def rsaFromFactorStep (n : ℕ) (s : List Bool) (N e y : ℕ) : List Bool :=
  if listToNat s * (N / listToNat s) = N then
    natToList (2 * n)
      (y ^ ((e : ZMod ((listToNat s - 1) * (N / listToNat s - 1)))⁻¹).val % N)
  else []

/-- **Algorithm 55.3 succeeds whenever the factor is right** [PS10, proof of Theorem 55.2,
"provided that the factors are correct, … this always succeeds with probability 1"]: if `s`
reads as `p` or `q`, then on `(N, e, y)` with `N = pq`, `gcd(e, Φ(N)) = 1` and `y ∈ Z_N^*`
the output decodes to a `2n`-bit numeral `x` with `x^e = y` in `Z_N`.

**Proof sketch.** `q' = N / p` is the other prime (`Nat.mul_div_cancel_left`), so the test
passes and `(p'−1)(q'−1) = Φ(N)` (`DistinctPrimes.totient_mul`); `d` satisfies
`ed ≡ 1 (mod Φ(N))` (`mul_inv_val_modEq`); the output is the numeral of
`y.val^d mod N = (y^d).val < N < 2^{2n}` (`val_units_pow`, `decodeFin_ofFn`,
`bitsToNat_natToBits`), and `(y^d)^e = y` by `rsa_pow_pow`. -/
theorem rsaFromFactorStep_correct {n : ℕ} (z : DistinctPrimes n) {s : List Bool}
    (hs : listToNat s = z.p ∨ listToNat s = z.q) {e : ℕ}
    (he : Nat.Coprime e (Nat.totient (z.p * z.q))) (y : (ZMod (z.p * z.q))ˣ) :
    ∃ x : Fin (2 * n) → Bool,
      decodeFin (2 * n) (rsaFromFactorStep n s (z.p * z.q) e (y : ZMod (z.p * z.q)).val) = some x ∧
        ((bitsToNat x : ℕ) : ZMod (z.p * z.q)) ^ e = (y : ZMod (z.p * z.q)) := by
  have hpq : listToNat s * (z.p * z.q / listToNat s) = z.p * z.q ∧
      (listToNat s - 1) * (z.p * z.q / listToNat s - 1) = Nat.totient (z.p * z.q) := by
    rcases hs with hs | hs <;> rw [hs]
    · rw [Nat.mul_div_cancel_left _ z.p_prime.pos, z.totient_mul]
      exact ⟨rfl, rfl⟩
    · rw [Nat.mul_div_cancel _ z.q_prime.pos, z.totient_mul]
      exact ⟨mul_comm _ _, mul_comm _ _⟩
  have he' : Nat.Coprime e ((listToNat s - 1) * (z.p * z.q / listToNat s - 1)) := by
    rw [hpq.2]; exact he
  have hed : e * ((e : ZMod ((listToNat s - 1) * (z.p * z.q / listToNat s - 1)))⁻¹).val ≡ 1
      [MOD Nat.totient (z.p * z.q)] := by
    unfold Nat.ModEq
    rw [← hpq.2]
    exact mul_inv_val_modEq e _ he'
  set d := ((e : ZMod ((listToNat s - 1) * (z.p * z.q / listToNat s - 1)))⁻¹).val
  have hv : (y : ZMod (z.p * z.q)).val ^ d % (z.p * z.q) < 2 ^ (2 * n) :=
    (Nat.mod_lt _ (NeZero.pos _)).trans z.mul_lt
  refine ⟨natToBits (2 * n) ((y : ZMod (z.p * z.q)).val ^ d % (z.p * z.q)), ?_, ?_⟩
  · rw [rsaFromFactorStep, if_pos hpq.1, natToList_eq]
    exact decodeFin_ofFn _
  · rw [bitsToNat_natToBits hv, ZMod.natCast_mod, Nat.cast_pow, ZMod.natCast_zmod_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm d e, pow_mul]
    exact congrArg Units.val (rsa_pow_pow hed y)

/-- The string function of `A'` [PS10, Algorithm 55.3] on the raw layout
`⟨⟨⟨1^n, ⟨N, ⟨e, y⟩⟩⟩, α⟩, r⟩`: run `A` on `⟨⟨⟨1^n, N⟩, α⟩, r⟩` (same coins and advice) and
apply `rsaFromFactorStep`. -/
def rsaFromFactorRaw (A : NUPPT) (z : List Bool) : List Bool :=
  rsaFromFactorStep (NUPPT.inParam z).length
    (A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (NUPPT.inAdvice z)
      (NUPPT.inCoins z)))
    (listToNat (pairFstD (NUPPT.inArg z))) (listToNat (pairFstD (pairSndD (NUPPT.inArg z))))
    (listToNat (pairSndD (pairSndD (NUPPT.inArg z))))

/-- **`A'` is polynomial-time** [PS10, Theorem 55.2, "the running time of `A'` is essentially
the running time of `A` plus `O(log³ n)`"] given the arithmetic bundle.

**Proof sketch.** `A.output` on the re-paired layout (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`); `q'` by `H.divMod`; the test `p' q' = N` by `H.mul` and
`polyTimeComputable_pairEq` (`polyTimeComputable_ite`); the decrements `p' − 1`, `q' − 1`
by `H.sub` with `[true]` (run-3 audit P7-1); `Φ` by `H.mul`; `d` as the second component of
`xgcdStr ⟨e, Φ⟩` (`H.xgcd`); `y^d mod N` by `H.modExp`; padding to `2n` bits by
`polyTimeComputable_unaryPoly`/`_blockMap`. -/
theorem polyTimeComputable_rsaFromFactorRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rsaFromFactorRaw A) := by
  sorry

/-- **The adversary `A'`** [PS10, Algorithm 55.3] as a non-uniform PPT with the coins and
advice of the factoring adversary `A`. -/
noncomputable def rsaFromFactorer (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_rsaFromFactorRaw H A) A.coins A.adv A.advice A.advice_length

/-- `rsaFromFactorer` has the coins of `A`. -/
@[simp] theorem coins_rsaFromFactorer (H : ArithmeticFP) (A : NUPPT) :
    (rsaFromFactorer H A).coins = A.coins := by
  unfold rsaFromFactorer
  exact NUPPT.coins_ofPolyTime _ _ _ _ _

/-- **`A'` runs on the coins of `A`**: the published equivalence
`(rsaFromFactorer H A).Coins n ≃ A.Coins n` (`NUPPT.coinsCongr` along `coins_rsaFromFactorer`). -/
noncomputable def rsaFromFactorer_coinsEquiv (H : ArithmeticFP) (A : NUPPT) (n : ℕ) :
    (rsaFromFactorer H A).Coins n ≃ A.Coins n :=
  NUPPT.coinsCongr (coins_rsaFromFactorer H A) n

/-- The coin equivalence keeps the coin string:
`List.ofFn (rsaFromFactorer_coinsEquiv H A n r) = List.ofFn r`. -/
theorem rsaFromFactorer_coinsEquiv_ofFn (H : ArithmeticFP) (A : NUPPT) (n : ℕ)
    (r : (rsaFromFactorer H A).Coins n) :
    List.ofFn (rsaFromFactorer_coinsEquiv H A n r) = List.ofFn r :=
  NUPPT.coinsCongr_ofFn (coins_rsaFromFactorer H A) n r

/-- The activation of `A'`: `A'(1^n, ⟨N, ⟨e, y⟩⟩; r) = rsaFromFactorStep n (A(1^n, N; φ r)) N e y`,
the coins read through `φ = rsaFromFactorer_coinsEquiv H A n`. -/
theorem rsaFromFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N e y : List Bool)
    (r : (rsaFromFactorer H A).Coins n) :
    (rsaFromFactorer H A).runAt n (pairEncode N (pairEncode e y)) r =
      rsaFromFactorStep n (A.runAt n N (rsaFromFactorer_coinsEquiv H A n r)) (listToNat N)
        (listToNat e) (listToNat y) := by
  rw [NUPPT.runAt_eq, rsaFromFactorer_coinsEquiv, NUPPT.runAt_coinsCongr]
  unfold rsaFromFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp only [NUPPT.runAtL_eq, NUPPT.layout_eq, NUPPT.inParam_eq, NUPPT.inArg_eq,
    NUPPT.inAdvice_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq, pairFstD_pairEncode,
    pairSndD_pairEncode, rsaFromFactorRaw, List.length_replicate]

/-- **A factorer gives an RSA breaker with the same probability** [PS10, proof of
Theorem 55.2]: `Pr[A factors N] ≤ Pr[A' breaks RSA]`.

**Proof sketch.** `rsaProb` averages over `z` the probability over `(e, y, r)`; for fixed
`z` and `r`, if `A(1^n, N; r)` reads as `p` or `q` then `A'` succeeds for *every* `(e, y)`
(`rsaFromFactorer_runAt`, `rsaFromFactorer_coinsEquiv`, `rsaFromFactorStep_correct`, `rsaInput`,
`listToNat_natToList`), so `Pr_{e,y,r}[A' wins | z] ≥ Pr_r[A factors | z]` (`uprob_mono`,
`uprob_fst`-style marginalization with the coordinates reordered by `uprob_comp_equiv`);
and `factorProb A n = uexp_z Pr_r[A factors | z]` (`uprob_prod`). -/
theorem factorProb_le_rsaProb (H : ArithmeticFP) (A : NUPPT) (n : ℕ) :
    factorProb A n ≤ rsaProb (rsaFromFactorer H A) n := by
  sorry

/-- **Theorem 55.2** [PS10, Theorem 55.2]: the RSA assumption implies the factoring
assumption (under the arithmetic hypotheses).

**Deviation:** both assumptions on uniform pairs of distinct primes of `Π_n`
(module docstring); the text's `n`/`k` mix-up is resolved as `n`.

**Proof sketch.** For every `A`, `factorProb A n ≤ rsaProb (rsaFromFactorer H A) n`
(`factorProb_le_rsaProb`), which is negligible by `hR`; conclude by `Negligible.mono`
(`factorProb_nonneg`). -/
theorem rsa_imp_factoring (H : ArithmeticFP) (hR : RSAAssumption) : FactoringAssumption := by
  sorry

end TCSlib.Cryptography.Candidates
