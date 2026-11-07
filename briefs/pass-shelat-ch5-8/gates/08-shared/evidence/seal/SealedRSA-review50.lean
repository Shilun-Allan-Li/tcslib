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
-- S1 SEAL: the foreign TCSlib definitions collected from the elaborated terms of the touched declarations, plus matchers (PolyExpr.eval and glNeed left unsealed)
attribute [local irreducible] _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.default _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.p _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.q _root_.TCSlib.Cryptography.Candidates.FactoringAssumption _root_.TCSlib.Cryptography.Candidates.divModStr _root_.TCSlib.Cryptography.Candidates.factorProb _root_.TCSlib.Cryptography.Candidates.leStr _root_.TCSlib.Cryptography.Candidates.modExpStr _root_.TCSlib.Cryptography.Candidates.modulusBits _root_.TCSlib.Cryptography.Candidates.mulStr _root_.TCSlib.Cryptography.Candidates.natToBits _root_.TCSlib.Cryptography.Candidates.natToList _root_.TCSlib.Cryptography.Candidates.primeStr _root_.TCSlib.Cryptography.Candidates.rejectBlocksL _root_.TCSlib.Cryptography.Candidates.samplePrimeL _root_.TCSlib.Cryptography.Candidates.sizeStr _root_.TCSlib.Cryptography.Candidates.subStr _root_.TCSlib.Cryptography.Candidates.xgcdStr _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.NumberTheory.listToNat _root_.TCSlib.Cryptography.NumberTheory.samplePrimeCoins _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode

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

/-- **The total unit sampler gives a unit**: for `0 < N`, the value
`(sampleUnitL N k B T r).getD (1 % N)` is below `N` and coprime to `N`:
`(sampleUnitL N k B T r).getD (1 % N) < N ∧ gcd((sampleUnitL N k B T r).getD (1 % N), N) = 1`
(`sampleUnitL_spec`, or the fallback `1 mod N`, which passes the unit test). -/
theorem sampleUnitL_getD_spec {N : ℕ} (hN : 0 < N) (k B T : ℕ) (r : List Bool) :
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
(3) The acceptance probability is `Φ(N)/2^k` (`uprob_def`, `Nat.card_congr` along the same
bijection, `ZMod.card_units_eq_totient`; `rsa_uprob_units`).
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

/-- **The unit test by comparisons**: for `N = ⟦w⟧`, "`¬ (N ≤ v)`, and the `|w|`-bit numeral `g`
of `gcd(v, N)` reads `≤ 1` and `≥ 1`" is the test `v < N ∧ gcd(v, N) = 1`.

**Proof sketch.** If `v < N` then `gcd(v, N) ≤ N < 2^{|w|}`, so `g` reads as the gcd
(`listToNat_natToList`), and "`≤ 1` and `≥ 1`" is "`= 1`", i.e. coprimality; if `v ≥ N` both
sides are false. -/
private theorem rsa_unitTest_eq (v : ℕ) (w : List Bool) :
    (!(decide (listToNat w ≤ v)) &&
      decide (listToNat (natToList w.length (Nat.gcd v (listToNat w))) ≤ listToNat [true]) &&
      decide (listToNat [true] ≤ listToNat (natToList w.length (Nat.gcd v (listToNat w))))) =
      decide (v < listToNat w ∧ Nat.Coprime v (listToNat w)) := by
  rw [listToNat_singleton_true]
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

/-- The acceptance test is polynomial-time (`polyTimeComputable_isNil`, `H.le`, `H.xgcd`).

**Proof sketch.** The gcd numeral is `H.xgcd` on `⟨block, w⟩` followed by `pairFstD`, stated in
applied form (`PolyTimeComputable.comp'`) and folded into `rsa_usGcd`; the four one-bit tests are
`polyTimeComputable_isNil` (negated), `H.le` (negated) and two `H.le` against `[true]`
(`ArithmeticFP.le_poly`); they are combined by `polyTimeComputable_and` with the tests given explicitly,
so that no bundle string function is unfolded by unification. -/
private theorem rsa_usAcc_poly (H : ArithmeticFP) :
    PolyTimeComputable fun x => [rsa_usAcc x] := by
  have hw : PolyTimeComputable fun x => pairSndD (pairSndD (pairFstD x)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
  have hx : PolyTimeComputable fun x =>
      xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x)))) :=
    PolyTimeComputable.comp' H.xgcd (rsa_usBlock_poly.pairEncode hw)
  have hg' : PolyTimeComputable fun x =>
      pairFstD (xgcdStr (pairEncode (rsa_usBlock x) (pairSndD (pairSndD (pairFstD x))))) :=
    PolyTimeComputable.comp' polyTimeComputable_pairFstD hx
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
    PolyTimeComputable.comp' polyTimeComputable_isNil hc
  have t1' : PolyTimeComputable fun x => [!decide (pairFstD (pairSndD x) = [])] :=
    polyTimeComputable_not (p := fun x => decide (pairFstD (pairSndD x) = [])) t1
  have t2 : PolyTimeComputable fun x =>
      [decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))] :=
    H.le_poly hw rsa_usBlock_poly
  have t2' : PolyTimeComputable fun x =>
      [!decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))] :=
    polyTimeComputable_not
      (p := fun x => decide (listToNat (pairSndD (pairSndD (pairFstD x))) ≤ listToNat (rsa_usBlock x))) t2
  have t3 : PolyTimeComputable fun x => [decide (listToNat (rsa_usGcd x) ≤ listToNat [true])] :=
    H.le_poly hg (polyTimeComputable_const [true])
  have t4 : PolyTimeComputable fun x => [decide (listToNat [true] ≤ listToNat (rsa_usGcd x))] :=
    H.le_poly (polyTimeComputable_const [true]) hg
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
`[0, |x| + 1) ⊇ [0, T)` is then the search over `[0, T)` (`IterateFind.find?_range_and_lt`), and
`sampleUnitL = rejectBlocksL` is that search followed by reading the block
(`rejectBlocksL_eq`, `rejectBlocksL_eq_find?`). -/
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
    exact IterateFind.find?_range_and_lt _ hrange
  rw [hfind, sampleUnitL_eq, rejectBlocksL_eq_find?]
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
`z ↦ unitSampleStr (f z) |inParam z| (inCoins z)` is polynomial-time.

**Proof sketch.** The trial loop on the start state is `rsa_usLoop_poly` composed with
`rsa_usStart_poly`; the value block is the loop result with its marker dropped
(`polyTimeComputable_tail`), or `[true]` when the loop finds nothing (`polyTimeComputable_isNil`,
`polyTimeComputable_ite`); the output is the remainder of `H.divMod ⟨block, w⟩`. It equals
`unitSampleStr` by `rsa_usFind_eq`: if no trial is accepted, `sampleUnitL` is `none` and the
remainder of `1` is the fallback `1 mod N`; if trial `i` is accepted, its value is below `N`
(`sampleUnitL_spec`) and is its own remainder. -/
private theorem rsa_ptc_unitSampleStr (H : ArithmeticFP) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
  -- the trial loop on the start state (the repetition host)
  have hL : PolyTimeComputable fun z => rsa_usLoop (rsa_usStart f z) :=
    PolyTimeComputable.comp' (rsa_usLoop_poly H) (rsa_usStart_poly H hf)
  have hN : PolyTimeComputable fun z => [decide (rsa_usLoop (rsa_usStart f z) = [])] :=
    PolyTimeComputable.comp' polyTimeComputable_isNil hL
  have hT : PolyTimeComputable fun z => (rsa_usLoop (rsa_usStart f z)).drop 1 :=
    PolyTimeComputable.comp' polyTimeComputable_tail hL
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
    PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (hG.pairEncode hf))
  have e : (fun z => pairSndD (divModStr (pairEncode
      (if decide (rsa_usLoop (rsa_usStart f z) = []) then [true]
        else (rsa_usLoop (rsa_usStart f z)).drop 1) (f z)))) =
      fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
    funext z
    rw [divModStr_pairEncode, pairSndD_pairEncode, unitSampleStr_eq, rsa_usFind_eq f z, rsa_usLoop]
    rcases hres : (List.range ((rsa_usStart f z).length + 1)).find?
        (fun i => rsa_usAcc (rsa_usStep^[i] (rsa_usStart f z))) with _ | i
    · rw [Option.elim_none, Option.map_none, Option.getD_none, if_pos (by rfl), listToNat_singleton_true]
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

/-- The numeral `[true, false]` reads as `2`. -/
private theorem rsa_listToNat_two : listToNat [true, false] = 2 := by
  rw [listToNat_eq]
  rfl

/-- The numeral `[true, true]` reads as `3`. -/
private theorem rsa_listToNat_three : listToNat [true, true] = 3 := by
  rw [listToNat_eq]
  rfl

/-- **Width normalization**: the remainder of `⟦x⟧` modulo the all-ones word `1^k` is the
`k`-bit numeral of `⟦x⟧` when `⟦x⟧ < 2^k − 1`. -/
private theorem rsa_norm (x : List Bool) (k : ℕ) (h : listToNat x < 2 ^ k - 1) :
    pairSndD (divModStr (pairEncode x (List.replicate k true))) = natToList k (listToNat x) := by
  rw [divModStr_pairEncode, pairSndD_pairEncode, List.length_replicate, listToNat_replicate_true,
    Nat.mod_eq_of_lt h]

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
  refine PolyTimeComputable.congr (PolyTimeComputable.comp' (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
  rw [pairFstD_pairEncode, pairSndD_pairEncode, rsa_gP]

/-- The second prime run is polynomial-time (S1 on `⟨1^M, (r.drop L).take L⟩`). -/
private theorem rsa_gQ_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gQ := by
  have hD : PolyTimeComputable fun y => pairEncode (pairFstD y)
      ((pairSndD y).drop (samplePrimeCoins.eval (pairFstD y).length)) :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairDropPoly samplePrimeCoins)
  have hT := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly samplePrimeCoins) hD
  have hA := polyTimeComputable_pairFstD.pairEncode hT
  refine PolyTimeComputable.congr (PolyTimeComputable.comp' (polyTimeComputable_samplePrimeL H.prime) hA) fun y => ?_
  simp only [pairFstD_pairEncode, pairSndD_pairEncode]
  rw [rsa_gQ]

/-- The validity test is polynomial-time.

**Proof sketch.** Two primality tests (`ArithmeticFP.prime_poly`, `H.prime`), the negated conjunction of
the comparisons `p ≤ q`, `q ≤ p`, and the comparisons of `p`, `q` with `⟦1^M⟧` (`ArithmeticFP.le_poly`),
combined by `polyTimeComputable_and` and `polyTimeComputable_not` with explicit tests. -/
private theorem rsa_gValid_poly (H : ArithmeticFP) : PolyTimeComputable fun y => [rsa_gValid y] := by
  have hP := rsa_gP_poly H
  have hQ := rsa_gQ_poly H
  have t1 := H.prime_poly hP
  have t2 := H.prime_poly hQ
  have t3 := H.le_poly hP hQ
  have t4 := H.le_poly hQ hP
  have t5 := H.le_poly hP polyTimeComputable_pairFstD
  have t6 := H.le_poly hQ polyTimeComputable_pairFstD
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
  have h1 := PolyTimeComputable.comp' H.sub ((rsa_gPw_poly H).1.pairEncode (polyTimeComputable_const [true]))
  have h2 := PolyTimeComputable.comp' H.sub ((rsa_gPw_poly H).2.pairEncode (polyTimeComputable_const [true]))
  have h := PolyTimeComputable.comp' H.mul (h1.pairEncode h2)
  unfold rsa_gPhi
  exact h

/-- The exponent word is polynomial-time: the unit sampler on the re-laid-out input
`layout 1^M ⟦Φ⟧ [] (r.drop 2L)` (`rsa_ptc_unitSampleStr`, `NUPPT.polyTimeComputable_layout`). -/
private theorem rsa_gE_poly (H : ArithmeticFP) : PolyTimeComputable rsa_gE := by
  have hl := NUPPT.polyTimeComputable_layout polyTimeComputable_pairFstD (rsa_gPhi_poly H)
    (polyTimeComputable_const []) (polyTimeComputable_pairDropPoly (.mul (.const 2) samplePrimeCoins))
  refine PolyTimeComputable.congr (PolyTimeComputable.comp' (rsa_ptc_unitSampleStr H NUPPT.polyTimeComputable_inArg) hl)
    fun y => ?_
  rw [NUPPT.inArg_layout, NUPPT.inParam_layout, NUPPT.inCoins_layout, rsa_gE]

/-- The normalization of a polynomial-time word is polynomial-time (`H.divMod`,
`polyTimeComputable_unaryPoly`). -/
private theorem rsa_gNorm_poly (H : ArithmeticFP) {x : List Bool → List Bool}
    (hx : PolyTimeComputable x) : PolyTimeComputable fun y => rsa_gNorm y (x y) := by
  have ho := PolyTimeComputable.comp' (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) polyTimeComputable_pairFstD
  have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.divMod (hx.pairEncode ho))
  unfold rsa_gNorm
  exact h

/-- The generator's string computation is polynomial-time. -/
private theorem rsa_genCore_poly (H : ArithmeticFP) : PolyTimeComputable rsa_genCore := by
  have hN := PolyTimeComputable.comp' H.mul ((rsa_gPw_poly H).1.pairEncode (rsa_gPw_poly H).2)
  have hD := PolyTimeComputable.comp' polyTimeComputable_pairSndD
    (PolyTimeComputable.comp' H.xgcd ((rsa_gE_poly H).pairEncode (rsa_gPhi_poly H)))
  have h := ((rsa_gNorm_poly H hN).pairEncode (rsa_gNorm_poly H (rsa_gE_poly H))).pairEncode
    ((rsa_gNorm_poly H hN).pairEncode (rsa_gNorm_poly H hD))
  unfold rsa_genCore
  exact h

/-- **The string computation is the generator**: on `⟨1^{max n 2}, r⟩` it outputs
`rsaGenOut n r`.

**Proof sketch.** With `M = max n 2` and `L = 2M³`, `rsa_gP`, `rsa_gQ` are the two prime runs
of `rsaGenParams`, and the validity test is its condition (`⟦1^M⟧ = 2^M − 1`; two comparisons
for `p ≠ q`), so the prime words read as the primes of the parameters (`default_p`,
`default_q` on the fallback). Then `⟦N⟧ = pq` (`listToNat_mulStr`), `⟦Φ⟧ = (p−1)(q−1) =
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
    rw [hy1, listToNat_replicate_true]
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
    rw [listToNat_mulStr, ← hzp.1, ← hzp.2]
    rfl
  have hPhi : listToNat (rsa_gPhi y) =
      Nat.totient ((rsaGenParams n r).z.p * (rsaGenParams n r).z.q) := by
    rw [rsa_gPhi, listToNat_mulStr, listToNat_subStr, listToNat_subStr, listToNat_singleton_true,
      ← hzp.1, ← hzp.2, DistinctPrimes.totient_mul]
  have hΦ1 := (rsaGenParams n r).z.one_lt_totient
  have he : listToNat (rsa_gE y) = (rsaGenParams n r).e := by
    have hv := sampleUnitL_getD_spec (N := listToNat (rsa_gPhi y)) (by omega) (Nat.size (listToNat (rsa_gPhi y)))
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
    refine PolyTimeComputable.congr (PolyTimeComputable.comp' polyTimeComputable_lenLe
      ((polyTimeComputable_const [true]).pairEncode NUPPT.polyTimeComputable_inParam)) fun z => ?_
    rw [pairFstD_pairEncode, pairSndD_pairEncode, List.length_singleton]
  have hun : PolyTimeComputable fun z => List.replicate (NUPPT.inParam z).length true := by
    refine PolyTimeComputable.congr (PolyTimeComputable.comp' (polyTimeComputable_unaryPoly .var) NUPPT.polyTimeComputable_inParam)
      fun z => ?_
    rw [PolyExpr.eval_var]
  have hu := polyTimeComputable_ite (p := fun z => decide ((NUPPT.inParam z).length ≤ 1))
    (f := fun _ => [true, true]) (g := fun z => List.replicate (NUPPT.inParam z).length true)
    hle (polyTimeComputable_const _) hun
  have h := PolyTimeComputable.comp' (rsa_genCore_poly H) (hu.pairEncode NUPPT.polyTimeComputable_inCoins)
  refine PolyTimeComputable.congr h fun z => ?_
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
`sampleUnitL_getD_spec`). -/
private theorem rsa_dec_unitSampleStr {m : ℕ} (P : RSAParams m) (n : ℕ) (r : List Bool) :
    ∃ x, rsaDec (rsaIndexOf m P) (unitSampleStr (pairFstD (rsaIndexOf m P)) n r) = some x := by
  have hw : pairFstD (rsaIndexOf m P) = natToList (2 * m) P.N := by
    rw [rsaIndexOf, pairFstD_pairEncode]
  have hN : listToNat (natToList (2 * m) P.N) = P.N := listToNat_natToList P.N_lt
  have hpos : 0 < P.N := NeZero.pos (P.z.p * P.z.q)
  have hv := sampleUnitL_getD_spec hpos (Nat.size P.N) (rsaBlock.eval n) (rsaTrials.eval n) r
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
`length_natToList`, `listToNat_natToList` (`v < N < 2^{2m}`), `sampleUnitL_spec` resp. the
default `1 % N` (`sampleUnitL_getD_spec`, `rsa_dec_unitSampleStr`); the decoded unit `x` re-encodes to the
sampler's string (`rsaEnc_of_rsaDec`), so `rsaEval_spec` applies. -/
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

**Proof sketch.** Take `δ n := 1` for `n < 2` and `δ n := e^{-n}` for `n ≥ 2`; it is negligible
(`exp_neg_le_half_pow`, `negligible_two_pow_neg`, `Negligible.mono`). The closeness `e^{-n}`
holds at every `n`, and `e^{-n} ≤ δ n` (`StatClose.mono`). Read the clause through
`Collection.sampleClose_iff`. At a generated index `⟨N, e⟩` (`rsaCollection_index`, valid by
`rsaValid_indexOf`) the sampler's output is `unitSampleStr` on the `2m`-bit numeral of `N`, with
`m = max n 2` (`rsa_sampler_runAt`, from `NUPPT.runAtL_ofPolyTimeUniform`). As `N < 2^{2m}`,
`Nat.size N ≤ 2m ≤ B(n)` at every `n`. So S3 (`statClose_sampleUnitL` at `N`) applies, and
mapping both sides by `v ↦ rsaDec i ⟦v⟧_{2m}` turns the residue of a uniform unit `x` into
`some x`, because `⟦x.val⟧_{2m} = rsaEnc i x` at a valid index (`rsaDec_rsaEnc`;
`rsa_statClose_dec`, `StatClose.map`). Transport along the sampler's coins
(`NUPPT.coinsEquivPoly`, `StatClose.comp_equiv_left`) and the domain
(`rsaCollection_domEquiv`, `rsaCollection_decD`, `StatClose.comp_equiv_right`). -/
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

/-! ### The inversion experiment against the RSA experiment (helpers of `rsaCollection_invProbAt_le`) -/

/-- The modulus of generated parameters is nonzero (a local instance: it is not exported). -/
private local instance rsa_neZero_N {m : ℕ} (P : RSAParams m) : NeZero P.N := DistinctPrimes.neZero_mul P.z

/-- The RSA event of `A` at modulus `M`, exponent `e` and challenge and coins `ρ = (y, ω)`: the
answer of `A` on `⟨⟦M⟧, ⟨⟦e⟧, ⟦y⟧⟩⟩` (`2n`-bit numerals) decodes to a `2n`-bit `x` with
`x^e = y` in `Z_M`. -/
private def rsa_T (A : NUPPT) (n M e : ℕ) (ρ : (ZMod M)ˣ × A.Coins n) : Prop :=
  ∃ x : Fin (2 * n) → Bool,
    decodeFin (2 * n) (A.runAt n (pairEncode (natToList (2 * n) M)
      (pairEncode (natToList (2 * n) e) (natToList (2 * n) (ρ.1 : ZMod M).val))) ρ.2) = some x ∧
    ((bitsToNat x : ℕ) : ZMod M) ^ e = (ρ.1 : ZMod M)

/-- The RSA success probability of `A` at modulus `M` and exponent `e`, over the challenge
`y ∈ Z_M^*` and the coins. -/
private noncomputable def rsa_g (A : NUPPT) (n M e : ℕ) [NeZero M] : ℝ := uprob (rsa_T A n M e)

/-- `rsa_g` depends on the modulus only through its value (the `NeZero` instances agree). -/
private theorem rsa_g_congr (A : NUPPT) (n e : ℕ) {M M' : ℕ} (h : M = M') [NeZero M] [NeZero M'] :
    rsa_g A n M e = rsa_g A n M' e := by
  subst h
  rfl

/-- The encoding of the domain of the RSA collection is injective: `rsaF i` is the encoding of
the permutation `rsaPermAt i` (`rsaF_perm`, `rsaDec_rsaEnc`). -/
private theorem rsa_rsaF_injective (i : List Bool) : Function.Injective (rsaF i) := by
  intro x x' h
  rw [rsaF_perm, rsaF_perm] at h
  have h' := congrArg (rsaDec i) h
  rw [rsaDec_rsaEnc, rsaDec_rsaEnc, Option.some.injEq] at h'
  exact (rsaPermAt i).injective h'

/-- **An inversion is an RSA success** (step (o) of `rsaCollection_invProbAt_le`): at the index
`i = ⟨N, e⟩` generated from `P` (`n ≥ 2`), if `A(1^n, ⟨i, f_i(u)⟩; ω)` decodes to a preimage of
`f_i(u)`, then `A' = rsaBreaker A` succeeds on the challenge `y = u^e` with the coins
`φ⁻¹ ω`.

**Proof sketch.** The preimage is `u` (`rsa_rsaF_injective`), so the answer is
`rsaEnc i u = ⟦u⟧_{2n}` (`rsaEnc_of_rsaDec`, valid index); `A'` re-pairs its input into
`⟨⟨⟦N⟧, ⟦e⟧⟩, ⟦u^e⟧⟩ = ⟨i, f_i(u)⟩` (`rsaBreaker_runAt`, `rsaF_perm`), and the decoded answer
`x = ⟦u⟧` satisfies `x^e = u^e` (`bitsToNat_natToBits`, `ZMod.natCast_zmod_val`). -/
private theorem rsa_inv_imp {n : ℕ} (hn : 2 ≤ n) (A : NUPPT) (P : RSAParams (max n 2))
    (u : (ZMod (rsaMod (rsaIndexOf _ P)))ˣ) (ω : A.Coins n)
    (h : ∃ x', rsaDec (rsaIndexOf _ P)
        (A.runAt n (pairEncode (rsaIndexOf _ P) (rsaF (rsaIndexOf _ P) u)) ω) = some x' ∧
      rsaF (rsaIndexOf _ P) x' = rsaF (rsaIndexOf _ P) u) :
    rsa_T (rsaBreaker A) n (rsaMod (rsaIndexOf _ P)) P.e
      (rsaPermAt (rsaIndexOf _ P) u, (rsaBreaker_coinsEquiv A n).symm ω) := by
  obtain ⟨x', hx', hf⟩ := h
  rw [rsa_rsaF_injective _ hf] at hx'
  have hv := rsaValid_indexOf _ P
  have hmx : max n 2 = n := max_eq_left hn
  have hlen : (pairFstD (rsaIndexOf _ P)).length = 2 * n := by
    rw [rsaIndexOf, pairFstD_pairEncode, length_natToList, hmx]
  have hw := rsaEnc_of_rsaDec hx'
  rw [rsaEnc, rsaEncVal, if_pos hv, hlen] at hw
  have hfu : rsaF (rsaIndexOf _ P) u = natToList (2 * n)
      ((rsaPermAt (rsaIndexOf _ P) u : ZMod (rsaMod (rsaIndexOf _ P)))).val := by
    rw [rsaF_perm, rsaEnc, rsaEncVal, if_pos hv, hlen]
  have hi : pairEncode (natToList (2 * n) (rsaMod (rsaIndexOf _ P))) (natToList (2 * n) P.e) =
      rsaIndexOf _ P := by
    have h2 : 2 * max n 2 = 2 * n := by rw [hmx]
    rw [rsaMod_indexOf, rsaIndexOf, h2]
  have hlt : (u : ZMod (rsaMod (rsaIndexOf _ P))).val < 2 ^ (2 * n) := hlen ▸ val_lt_two_pow _ u
  refine ⟨natToBits (2 * n) (u : ZMod (rsaMod (rsaIndexOf _ P))).val, ?_, ?_⟩
  · rw [rsaBreaker_runAt, Equiv.apply_symm_apply, hi, ← hfu, ← hw, natToList_eq]
    exact decodeFin_ofFn _
  · have he : rsaE (rsaIndexOf _ P) = P.e := rsaE_indexOf _ P
    rw [bitsToNat_natToBits hlt, ZMod.natCast_zmod_val, rsaPermAt, dif_pos hv, rsaPerm_apply, he,
      Units.val_pow_eq_pow_val]

/-- **The inversion probability at one generated index is at most an RSA probability**: for
`n ≥ 2`, the inner probability of `invProbAt` at the coins `r` of the generator is at most the
RSA success probability of `rsaBreaker A` at the modulus `N` and exponent `e` of
`rsaGenParams n r`.

**Proof sketch.** Read the domain through `rsaCollection_domEquiv` (`uprob_comp_equiv`); by
`rsa_inv_imp` the inversion event at `(u, ω)` implies the RSA event at
`(u^e, φ⁻¹ ω)`, and `(u, ω) ↦ (u^e, φ⁻¹ ω)` is a bijection (`rsaPermAt`,
`rsaBreaker_coinsEquiv`); the modulus `rsaMod i` is `N` (`rsaMod_indexOf`, `rsa_g_congr`). -/
private theorem rsa_inner_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n)
    (r : (rsaCollection H).gen.Coins n) :
    (uprob fun z : (rsaCollection H).D ((rsaCollection H).index n r) × A.Coins n =>
      ∃ x', (rsaCollection H).decD ((rsaCollection H).index n r)
          (A.runAt n (pairEncode ((rsaCollection H).index n r)
            ((rsaCollection H).f ((rsaCollection H).index n r) z.1)) z.2) = some x' ∧
        (rsaCollection H).f ((rsaCollection H).index n r) x' =
          (rsaCollection H).f ((rsaCollection H).index n r) z.1) ≤
      rsa_g (rsaBreaker A) n (rsaGenParams n (List.ofFn r)).N (rsaGenParams n (List.ofFn r)).e := by
  rw [rsaCollection_index]
  generalize rsaGenParams n (List.ofFn r) = P
  set φ := rsaCollection_domEquiv H (rsaIndexOf _ P)
  rw [← rsa_g_congr (rsaBreaker A) n P.e (rsaMod_indexOf _ P), rsa_g]
  refine le_of_le_of_eq ?_ (uprob_comp_equiv (Equiv.prodCongr (rsaPermAt (rsaIndexOf _ P))
      (rsaBreaker_coinsEquiv A n).symm) _)
  rw [← uprob_comp_equiv (Equiv.prodCongr φ.symm (Equiv.refl (A.Coins n)))]
  apply uprob_mono
  rintro ⟨u, ω⟩ h
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, rsaCollection_f,
    rsaCollection_decD] at h ⊢
  obtain ⟨x', hx', hf⟩ := h
  rw [Option.map_eq_some_iff] at hx'
  obtain ⟨v, hv, rfl⟩ := hx'
  rw [Equiv.apply_symm_apply] at hf
  exact rsa_inv_imp hn A P u ω ⟨v, hv, hf⟩

/-- The selection of the generator's primes from the two runs' values `(a, b)` at width `k`:
`(a, b)` if both are primes below `2^k` and distinct, the fallback `(2, 3)` otherwise. -/
private def rsa_zsel (k : ℕ) (ab : ℕ × ℕ) : ℕ × ℕ :=
  if ab.1.Prime ∧ ab.2.Prime ∧ ab.1 ≠ ab.2 ∧ ab.1 < 2 ^ k ∧ ab.2 < 2 ^ k then ab else (2, 3)

/-- **The generator's primes are the selection of the two runs' values** (`rsaGenParams`, its
fallback `DistinctPrimes.default`). -/
private theorem rsa_genParams_z (m : ℕ) (r : List Bool) :
    ((rsaGenParams m r).z.p, (rsaGenParams m r).z.q) = rsa_zsel (max m 2)
      (listToNat (samplePrimeL (max m 2) (r.take (samplePrimeCoins.eval (max m 2)))),
        listToNat (samplePrimeL (max m 2) ((r.drop (samplePrimeCoins.eval (max m 2))).take
          (samplePrimeCoins.eval (max m 2))))) := by
  unfold rsaGenParams
  dsimp only
  split
  · next hc =>
    rw [rsa_zsel, if_pos hc, DistinctPrimes.p_eq, DistinctPrimes.q_eq]
  · next hc =>
    rw [rsa_zsel, if_neg hc, DistinctPrimes.default_p, DistinctPrimes.default_q]

/-- The pair of distinct primes of a selected pair (for `2 ≤ k`): the selection when it is
valid, `DistinctPrimes.default` otherwise. -/
private def rsa_zOf {k : ℕ} (hk : 2 ≤ k) (ab : ℕ × ℕ) : DistinctPrimes k :=
  if h : ab.1.Prime ∧ ab.2.Prime ∧ ab.1 ≠ ab.2 ∧ ab.1 < 2 ^ k ∧ ab.2 < 2 ^ k then
    ⟨(⟨⟨ab.1, h.2.2.2.1⟩, h.1⟩, ⟨⟨ab.2, h.2.2.2.2⟩, h.2.1⟩), h.2.2.1⟩
  else DistinctPrimes.default hk

/-- The primes of `rsa_zOf` are the selection: `((rsa_zOf ab).p, (rsa_zOf ab).q) = rsa_zsel k ab`. -/
private theorem rsa_zOf_pq {k : ℕ} (hk : 2 ≤ k) (ab : ℕ × ℕ) :
    ((rsa_zOf hk ab).p, (rsa_zOf hk ab).q) = rsa_zsel k ab := by
  unfold rsa_zOf rsa_zsel
  split
  · next hc => rw [DistinctPrimes.p_eq, DistinctPrimes.q_eq]
  · next hc => rw [DistinctPrimes.default_p, DistinctPrimes.default_q]

/-- A pair of distinct primes is its own selection: `rsa_zOf (z.p, z.q) = z`. -/
private theorem rsa_zOf_self {k : ℕ} (hk : 2 ≤ k) (z : DistinctPrimes k) : rsa_zOf hk (z.p, z.q) = z := by
  have hc : (z.p, z.q).1.Prime ∧ (z.p, z.q).2.Prime ∧ (z.p, z.q).1 ≠ (z.p, z.q).2 ∧
      (z.p, z.q).1 < 2 ^ k ∧ (z.p, z.q).2 < 2 ^ k := ⟨z.p_prime, z.q_prime, z.p_ne_q, z.p_lt, z.q_lt⟩
  have h := rsa_zOf_pq hk (z.p, z.q)
  rw [rsa_zsel, if_pos hc, Prod.mk.injEq] at h
  exact DistinctPrimes.ext h.1 h.2

/-- The coin length of the generator: `2 · 2n³ + T(n) B(n) = rsaGenCoins(n)`. -/
private theorem rsa_genCoins_len (n : ℕ) :
    2 * (2 * n ^ 2 * n) + rsaSampleCoins.eval n = rsaGenCoins.eval n := by
  rw [rsaGenCoins, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, eval_samplePrimeCoins]

/-- The coin polynomial of the collection's generator is `rsaGenCoins`. -/
private theorem rsa_coins_gen (H : ArithmeticFP) : (rsaCollection H).gen.coins = rsaGenCoins := by
  rw [rsaCollection_gen]
  unfold rsaGen
  exact NUPPT.coins_ofPolyTimeUniform _ _

/-- The generator's coins are the two prime segments (`2 · 2n³` bits) followed by the exponent
segment: the equivalence `(Fin (2 · 2n³) → Bool) × (Fin (T(n) B(n)) → Bool) ≃ (rsaGen H).Coins n`
with `ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂` (Mathlib's `Fin.appendEquiv`, then the length
cast). -/
private noncomputable def rsa_genCoinsEquiv (H : ArithmeticFP) (n : ℕ) :
    (Fin (2 * (2 * n ^ 2 * n)) → Bool) × (Fin (rsaSampleCoins.eval n) → Bool) ≃
      (rsaCollection H).gen.Coins n :=
  (Fin.appendEquiv _ _).trans ((Equiv.arrowCongr (finCongr (rsa_genCoins_len n)) (Equiv.refl Bool)).trans
    (NUPPT.coinsEquivPoly (rsa_coins_gen H) n).symm)

/-- The coin string of the split coins is the concatenation of the segments. -/
private theorem rsa_genCoinsEquiv_ofFn (H : ArithmeticFP) (n : ℕ)
    (s : (Fin (2 * (2 * n ^ 2 * n)) → Bool) × (Fin (rsaSampleCoins.eval n) → Bool)) :
    List.ofFn (rsa_genCoinsEquiv H n s) = List.ofFn s.1 ++ List.ofFn s.2 := by
  unfold rsa_genCoinsEquiv
  rw [Equiv.trans_apply, Equiv.trans_apply, NUPPT.coinsEquivPoly_symm_ofFn]
  rw [show ((finCongr (rsa_genCoins_len n)).arrowCongr (Equiv.refl Bool))
      ((Fin.appendEquiv _ _) s) = fun i => (Fin.appendEquiv _ _) s (Fin.cast (rsa_genCoins_len n).symm i)
    from rfl, ← List.ofFn_congr (rsa_genCoins_len n)]
  exact List.ofFn_fin_append _ _

/-- The values of the two prime runs on the prime segment `s₁` of `2 · 2n³` coins (the sampler of
S2). -/
private def rsa_pr (n : ℕ) (s₁ : Fin (2 * (2 * n ^ 2 * n)) → Bool) : ℕ × ℕ :=
  (listToNat (samplePrimeL n ((List.ofFn s₁).take (2 * n ^ 2 * n))),
    listToNat (samplePrimeL n ((List.ofFn s₁).drop (2 * n ^ 2 * n))))

/-- The exponent sampled modulo `Φ(pq)` from the exponent segment `s₂` (the sampler of S3). -/
private def rsa_eNum {n : ℕ} (z : DistinctPrimes n) (s₂ : Fin (rsaSampleCoins.eval n) → Bool) : ℕ :=
  (sampleUnitL (Nat.totient (z.p * z.q)) (Nat.size (Nat.totient (z.p * z.q))) (rsaBlock.eval n)
    (rsaTrials.eval n) (List.ofFn s₂)).getD (1 % Nat.totient (z.p * z.q))

/-- **The generator on split coins** (`n ≥ 2`): on `E (s₁, s₂)` the modulus is `pq` for the pair
`z = rsa_zOf (rsa_pr s₁)` and the exponent is `rsa_eNum z s₂`, so the RSA probability at the
generated parameters is the one at `(z, rsa_eNum z s₂)`.

**Proof sketch.** `ofFn (E (s₁, s₂)) = ofFn s₁ ++ ofFn s₂` (`rsa_genCoinsEquiv_ofFn`), so the
two prime runs read `s₁` (`List.take_append_of_le_length`, `List.drop_append_of_le_length`,
`List.take_of_length_le`) and the exponent run reads `s₂` (`List.drop_left'`);
`rsa_genParams_z`, `rsa_zOf_pq` and `max n 2 = n` identify the primes, and the fallback of the
exponent is `1 = 1 mod Φ` (`DistinctPrimes.one_lt_totient`); `rsa_g_congr`. -/
private theorem rsa_g_split (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n)
    (s : (Fin (2 * (2 * n ^ 2 * n)) → Bool) × (Fin (rsaSampleCoins.eval n) → Bool)) :
    rsa_g A n (rsaGenParams n (List.ofFn (rsa_genCoinsEquiv H n s))).N
        (rsaGenParams n (List.ofFn (rsa_genCoinsEquiv H n s))).e =
      rsa_g A n ((rsa_zOf hn (rsa_pr n s.1)).p * (rsa_zOf hn (rsa_pr n s.1)).q)
        (rsa_eNum (rsa_zOf hn (rsa_pr n s.1)) s.2) := by
  rw [rsa_genCoinsEquiv_ofFn]
  obtain ⟨s₁, s₂⟩ := s
  have hmx : max n 2 = n := max_eq_left hn
  have hL1 : (List.ofFn s₁).length = 2 * (2 * n ^ 2 * n) := List.length_ofFn
  have hz := rsa_genParams_z n (List.ofFn s₁ ++ List.ofFn s₂)
  have hsel : rsa_zsel (max n 2)
      (listToNat (samplePrimeL (max n 2) ((List.ofFn s₁ ++ List.ofFn s₂).take
        (samplePrimeCoins.eval (max n 2)))),
        listToNat (samplePrimeL (max n 2) (((List.ofFn s₁ ++ List.ofFn s₂).drop
          (samplePrimeCoins.eval (max n 2))).take (samplePrimeCoins.eval (max n 2))))) =
      ((rsa_zOf hn (rsa_pr n s₁)).p, (rsa_zOf hn (rsa_pr n s₁)).q) := by
    rw [rsa_zOf_pq, rsa_pr, hmx, eval_samplePrimeCoins,
      List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega),
      List.take_of_length_le (l := (List.ofFn s₁).drop (2 * n ^ 2 * n))
        (by rw [List.length_drop]; omega)]
  rw [hsel, Prod.mk.injEq] at hz
  have hN : (rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).N =
      (rsa_zOf hn (rsa_pr n s₁)).p * (rsa_zOf hn (rsa_pr n s₁)).q := by
    rw [← hz.1, ← hz.2]
    rfl
  have he0 : (rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).e =
      (sampleUnitL (Nat.totient ((rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.p *
          (rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.q))
        (Nat.size (Nat.totient ((rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.p *
          (rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.q)))
        (rsaBlock.eval (max n 2)) (rsaTrials.eval (max n 2))
        ((List.ofFn s₁ ++ List.ofFn s₂).drop (2 * samplePrimeCoins.eval (max n 2)))).getD 1 := rfl
  have hΦ1 := (rsa_zOf hn (rsa_pr n s₁)).one_lt_totient
  have he1 : (sampleUnitL (Nat.totient ((rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.p *
          (rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.q))
        (Nat.size (Nat.totient ((rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.p *
          (rsaGenParams n (List.ofFn s₁ ++ List.ofFn s₂)).z.q)))
        (rsaBlock.eval (max n 2)) (rsaTrials.eval (max n 2))
        ((List.ofFn s₁ ++ List.ofFn s₂).drop (2 * samplePrimeCoins.eval (max n 2)))).getD 1 =
      rsa_eNum (rsa_zOf hn (rsa_pr n s₁)) s₂ := by
    rw [rsa_eNum, hz.1, hz.2, hmx, eval_samplePrimeCoins, Nat.mod_eq_of_lt hΦ1,
      List.drop_left' hL1]
  rw [he0, he1]
  exact rsa_g_congr A n _ hN

/-- The RSA probability at a pair `z`, averaged over a uniform exponent `e ∈ Z*_{Φ(N)}`. -/
private noncomputable def rsa_F (A : NUPPT) (n : ℕ) (z : DistinctPrimes n) : ℝ :=
  uexp fun eU : (ZMod (Nat.totient (z.p * z.q)))ˣ =>
    rsa_g A n (z.p * z.q) (eU : ZMod (Nat.totient (z.p * z.q))).val

/-- The RSA probability is the average of `rsa_F` over the pair `z` (`uprob_prod`). -/
private theorem rsa_rsaProb_eq (A : NUPPT) (n : ℕ) : rsaProb A n = uexp (rsa_F A n) := by
  unfold rsaProb rsa_F
  congr 1
  funext z
  rw [uprob_prod]
  rfl

/-- **Step (i): the exponent sampler** (S3 at the modulus `Φ(N)`): for a fixed pair `z`, the
average over the exponent segment of the RSA probability at the sampled exponent exceeds
`rsa_F z` by at most `e^{-n}`.

**Proof sketch.** `statClose_sampleUnitL` at `Φ(N)` (`Nat.size Φ(N) ≤ 2n ≤ B(n)`) and
`StatClose.abs_uprob_sub_le_prod` with the challenge and coins as auxiliary coins; both sides
are averages of `rsa_g` (`uprob_prod`). -/
private theorem rsa_step_i (A : NUPPT) {n : ℕ} (z : DistinctPrimes n) :
    uexp (fun s₂ : Fin (rsaSampleCoins.eval n) → Bool => rsa_g A n (z.p * z.q) (rsa_eNum z s₂)) ≤
      rsa_F A n z + Real.exp (-(n : ℝ)) := by
  have hk : Nat.size (Nat.totient (z.p * z.q)) ≤ rsaBlock.eval n := by
    rw [eval_rsaBlock]
    exact (Nat.size_le.2 ((Nat.totient_le _).trans_lt z.mul_lt)).trans (by omega)
  have h := (statClose_sampleUnitL n (Nat.totient (z.p * z.q)) hk).abs_uprob_sub_le_prod
    (fun e ρ => rsa_T A n (z.p * z.q) e ρ)
  have e1 : uprob (fun w : (Fin (rsaSampleCoins.eval n) → Bool) × ((ZMod (z.p * z.q))ˣ × A.Coins n) =>
      rsa_T A n (z.p * z.q) (rsa_eNum z w.1) w.2) =
      uexp (fun s₂ => rsa_g A n (z.p * z.q) (rsa_eNum z s₂)) := by
    rw [uprob_prod]
    rfl
  have e2 : uprob (fun w : (ZMod (Nat.totient (z.p * z.q)))ˣ × ((ZMod (z.p * z.q))ˣ × A.Coins n) =>
      rsa_T A n (z.p * z.q) (w.1 : ZMod (Nat.totient (z.p * z.q))).val w.2) = rsa_F A n z := by
    rw [uprob_prod]
    rfl
  have h' : |uprob (fun w : (Fin (rsaSampleCoins.eval n) → Bool) × ((ZMod (z.p * z.q))ˣ × A.Coins n) =>
      rsa_T A n (z.p * z.q) (rsa_eNum z w.1) w.2) -
      uprob (fun w : (ZMod (Nat.totient (z.p * z.q)))ˣ × ((ZMod (z.p * z.q))ˣ × A.Coins n) =>
        rsa_T A n (z.p * z.q) (w.1 : ZMod (Nat.totient (z.p * z.q))).val w.2)| ≤
      Real.exp (-(n : ℝ)) := h
  rw [e1, e2] at h'
  linarith [(abs_le.1 h').2]

/-- The auxiliary coins of the RSA experiment at a pair `z`: exponent, challenge and coins. -/
private abbrev rsa_Aux (A : NUPPT) (n : ℕ) (z : DistinctPrimes n) : Type :=
  (ZMod (Nat.totient (z.p * z.q)))ˣ × ((ZMod (z.p * z.q))ˣ × A.Coins n)

/-- Reading one coordinate of a uniform family of independent auxiliary coins is uniform:
`Pr_{ω ∈ Π_z Aux z}[Q (ω c)] = Pr_{a ∈ Aux c}[Q a]` (`Equiv.piSplitAt`, `uprob_fst`). -/
private theorem rsa_uprob_pi_eval (A : NUPPT) (n : ℕ) (c : DistinctPrimes n) (Q : rsa_Aux A n c → Prop) :
    uprob (fun ω : (z : DistinctPrimes n) → rsa_Aux A n z => Q (ω c)) = uprob Q := by
  have h := uprob_comp_equiv (Equiv.piSplitAt c (rsa_Aux A n)) (fun w => Q w.1)
  rw [uprob_fst] at h
  exact h

/-- **Step (ii): the prime sampler** (S2): the average of `rsa_F` over the prime segment, at the
selected pair, exceeds its average over a uniform pair by at most `2 (1/2)^n + 2n/2^n`.

**Proof sketch.** S2 mapped through the selection `rsa_zOf` (`StatClose.map`; a uniform pair is
its own selection, `rsa_zOf_self`); `rsa_F z` is a probability over the auxiliary coins
`ω z` of a uniform family `ω ∈ Π_z Aux z` (`rsa_uprob_pi_eval`, `uprob_prod`), so
`StatClose.abs_uprob_sub_le_prod` applies with `ω` as the auxiliary coins. -/
private theorem rsa_step_ii (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    uexp (fun s₁ : Fin (2 * (2 * n ^ 2 * n)) → Bool => rsa_F A n (rsa_zOf hn (rsa_pr n s₁))) ≤
      uexp (rsa_F A n) + (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) := by
  have hX := (statClose_samplePrimeL_pair n hn).map (rsa_zOf hn)
  rw [show (fun z : DistinctPrimes n => rsa_zOf hn (z.p, z.q)) = fun z => z from
    funext (rsa_zOf_self hn)] at hX
  have hX' : StatClose (fun s₁ => rsa_zOf hn (rsa_pr n s₁)) (fun z : DistinctPrimes n => z)
      (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) := hX
  let R : DistinctPrimes n → ((z : DistinctPrimes n) → rsa_Aux A n z) → Prop := fun γ ω =>
    rsa_T A n (γ.p * γ.q) ((ω γ).1 : ZMod (Nat.totient (γ.p * γ.q))).val (ω γ).2
  have hF : ∀ z, rsa_F A n z = uprob (fun ω : (z : DistinctPrimes n) → rsa_Aux A n z => R z ω) := by
    intro z
    rw [rsa_uprob_pi_eval A n z (fun a => rsa_T A n (z.p * z.q)
      (a.1 : ZMod (Nat.totient (z.p * z.q))).val a.2), uprob_prod]
    rfl
  have h := hX'.abs_uprob_sub_le_prod R
  have e1 : uprob (fun w : (Fin (2 * (2 * n ^ 2 * n)) → Bool) × ((z : DistinctPrimes n) → rsa_Aux A n z) =>
      R (rsa_zOf hn (rsa_pr n w.1)) w.2) =
      uexp (fun s₁ => rsa_F A n (rsa_zOf hn (rsa_pr n s₁))) := by
    rw [uprob_prod]
    congr 1
    funext s₁
    rw [hF]
  have e2 : uprob (fun w : DistinctPrimes n × ((z : DistinctPrimes n) → rsa_Aux A n z) => R w.1 w.2) =
      uexp (rsa_F A n) := by
    rw [uprob_prod]
    congr 1
    funext z
    rw [hF]
  rw [e1, e2] at h
  linarith [(abs_le.1 h).2]

/-- **Inverting the RSA collection breaks the RSA assumption** [PS10, proof of Theorem 53.2]:
for `n ≥ 2`, the inversion probability of `A` against the RSA collection is at most the RSA
probability of `rsaBreaker A` plus the statistical error of the generator.

**Proof sketch.** At a generated index `⟨N, e⟩` (`rsaCollection_index`, valid), the domain
is `Z_N^*` (`rsaMod_indexOf`), `f_{N,e}(x)` is the numeral of `(x^e).val` (`rsaF_perm`,
`rsaEnc`), and a decoded answer `x'` with `f x' = f x` has `x' = x` (`rsa_rsaF_injective`:
`rsaF_perm`, `rsaDec_rsaEnc`), so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of
`x`", which implies the RSA event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`,
`rsaBreaker_coinsEquiv`, `decodeFin_ofFn`, `bitsToNat_natToBits`; `rsa_inv_imp`). Since
`(x, ω) ↦ (x^e, φ⁻¹ ω)` is a bijection (`rsaPermAt`, `rsaBreaker_coinsEquiv`;
`uprob_comp_equiv`, `uprob_mono`), the inner probability is at most the RSA inner probability
at `(z, e)`: a number `h(z, e) ∈ [0, 1]` (over `y` and `A`'s coins; `rsa_inner_le`).
The exponent group `Z*_{Φ(N)}` depends on `z`, so the generator's law is not compared with one
uniform product: the comparison is a conditional expectation over `z`. Split the generator's
coins into the two prime segments and the exponent segment (`rsaGenParams`,
`HardcoreBit.uexp_prod`, `uprob_prod`, `HardcoreBit.uexp_comp_equiv`). (i) For each fixed prime
pair `z`, the exponent drawn from the exponent segment (`sampleUnitL` modulo `Φ(N)`, fallback
`1 = 1 mod Φ(N)` as `Φ(N) ≥ 2`) is within `e^{-n}` of
the uniform element of `Z*_{Φ(N)}` (S3, `statClose_sampleUnitL` at the modulus `Φ(N)`), so
the conditional success at `z` exceeds `g(z) := E_{e uniform}[h(z, e)]` by at most `e^{-n}`
(`StatClose.abs_uprob_sub_le_prod`, with `(y, r)` as the auxiliary coins). (ii) The law of `z`
under the two prime segments is within `2 · 2^{-n} + 2n/2^n` of the uniform law on
`DistinctPrimes n` (S2, `statClose_samplePrimeL_pair`, mapped through the validity test and
its fallback `(2, 3)` by `StatClose.map`; a uniform pair passes the test unchanged); averaging
the `[0, 1]`-valued `g` over that law instead of the uniform one costs at
most that distance (`StatClose.abs_uprob_sub_le_prod` again, with `g(z)` read as a probability
over the auxiliary coins `ω : Π z', Z*_{Φ(N')} × Z_{N'}^* × A.Coins n` at `ω z`). (iii) Adding
the conditional exponent error, the inversion probability is at most
`uexp g + (2 · 2^{-n} + 2n/2^n) + e^{-n} = rsaProb (rsaBreaker A) n + rsaGenErr n`, as
`rsaProb` is the outer `uexp` over `z` of the inner probability over `(e, y, r)`. No error
beyond `rsaGenErr n` is needed. -/
theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
    (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
  rw [Collection.invProbAt_eq]
  calc _ ≤ uexp (fun r : (rsaCollection H).gen.Coins n => rsa_g (rsaBreaker A) n
          (rsaGenParams n (List.ofFn r)).N (rsaGenParams n (List.ofFn r)).e) :=
        OneWay.uexp_mono fun r => rsa_inner_le H A hn r
    _ = uexp (fun s => rsa_g (rsaBreaker A) n
          (rsaGenParams n (List.ofFn (rsa_genCoinsEquiv H n s))).N
          (rsaGenParams n (List.ofFn (rsa_genCoinsEquiv H n s))).e) :=
        (HardcoreBit.uexp_comp_equiv (rsa_genCoinsEquiv H n) _).symm
    _ = uexp (fun s : (Fin (2 * (2 * n ^ 2 * n)) → Bool) × (Fin (rsaSampleCoins.eval n) → Bool) =>
          rsa_g (rsaBreaker A) n ((rsa_zOf hn (rsa_pr n s.1)).p * (rsa_zOf hn (rsa_pr n s.1)).q)
            (rsa_eNum (rsa_zOf hn (rsa_pr n s.1)) s.2)) := by
        congr 1
        funext s
        exact rsa_g_split H (rsaBreaker A) hn s
    _ = uexp (fun s₁ : Fin (2 * (2 * n ^ 2 * n)) → Bool => uexp fun s₂ : Fin (rsaSampleCoins.eval n) → Bool =>
          rsa_g (rsaBreaker A) n ((rsa_zOf hn (rsa_pr n s₁)).p * (rsa_zOf hn (rsa_pr n s₁)).q)
            (rsa_eNum (rsa_zOf hn (rsa_pr n s₁)) s₂)) := HardcoreBit.uexp_prod _
    _ ≤ uexp (fun s₁ : Fin (2 * (2 * n ^ 2 * n)) → Bool =>
          rsa_F (rsaBreaker A) n (rsa_zOf hn (rsa_pr n s₁)) + Real.exp (-(n : ℝ))) :=
        OneWay.uexp_mono fun s₁ => rsa_step_i (rsaBreaker A) (rsa_zOf hn (rsa_pr n s₁))
    _ = uexp (fun s₁ : Fin (2 * (2 * n ^ 2 * n)) → Bool =>
          rsa_F (rsaBreaker A) n (rsa_zOf hn (rsa_pr n s₁))) + Real.exp (-(n : ℝ)) := by
        rw [HardcoreBit.uexp_add, OneWay.uexp_const]
    _ ≤ uexp (rsa_F (rsaBreaker A) n) + (2 * (1 / 2 : ℝ) ^ n + 2 * n / 2 ^ n) +
          Real.exp (-(n : ℝ)) := by
        linarith [rsa_step_ii (rsaBreaker A) hn]
    _ = rsaProb (rsaBreaker A) n + rsaGenErr n := by
        rw [rsa_rsaProb_eq, rsaGenErr]
        ring

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
  refine ⟨rsaCollection_sampleClose H, fun A => ?_⟩
  refine ((rsaAssumption_iff.1 hR (rsaBreaker A)).add negligible_rsaGenErr).mono ⟨2, fun n hn => ?_⟩
  have herr : 0 ≤ rsaGenErr n := by
    unfold rsaGenErr
    positivity
  rw [abs_of_nonneg (Collection.invProbAt_nonneg _ A n),
    abs_of_nonneg (add_nonneg (rsaProb_nonneg _ n) herr)]
  exact rsaCollection_invProbAt_le H A hn

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

/-! ### `A'` as a string computation (helpers of `polyTimeComputable_rsaFromFactorRaw`) -/

/-- The answer of `A` on `⟨1^n, N⟩` (coins and advice of the outer input). -/
private def rsa_fS (A : NUPPT) (z : List Bool) : List Bool :=
  A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (NUPPT.inAdvice z)
    (NUPPT.inCoins z))

/-- The cofactor word `⟦N / p'⟧` (`divModStr`, the width of `N`). -/
private def rsa_fQ (A : NUPPT) (z : List Bool) : List Bool :=
  pairFstD (divModStr (pairEncode (pairFstD (NUPPT.inArg z)) (rsa_fS A z)))

/-- The test `p' q' = N` by two comparisons. -/
private def rsa_fTest (A : NUPPT) (z : List Bool) : Bool :=
  decide (listToNat (mulStr (pairEncode (rsa_fS A z) (rsa_fQ A z))) ≤
      listToNat (pairFstD (NUPPT.inArg z))) &&
    decide (listToNat (pairFstD (NUPPT.inArg z)) ≤
      listToNat (mulStr (pairEncode (rsa_fS A z) (rsa_fQ A z))))

/-- The word of `Φ = (p' − 1)(q' − 1)`, behind one leading zero. -/
private def rsa_fPhi (A : NUPPT) (z : List Bool) : List Bool :=
  subStr (pairEncode [true] [true]) ++
    mulStr (pairEncode (subStr (pairEncode (rsa_fS A z) [true])) (subStr (pairEncode (rsa_fQ A z) [true])))

/-- The word of `d = e⁻¹ mod Φ` (`xgcdStr`). -/
private def rsa_fD (A : NUPPT) (z : List Bool) : List Bool :=
  pairSndD (xgcdStr (pairEncode (pairFstD (pairSndD (NUPPT.inArg z))) (rsa_fPhi A z)))

/-- The word of `y^d mod N` (`modExpStr`), at the width `|y| + 1 + |N|` (leading zeros before `N`). -/
private def rsa_fV (A : NUPPT) (z : List Bool) : List Bool :=
  modExpStr (pairEncode (pairSndD (pairSndD (NUPPT.inArg z)))
    (pairEncode (rsa_fD A z)
      (subStr (pairEncode ([true] ++ pairSndD (pairSndD (NUPPT.inArg z)))
          ([true] ++ pairSndD (pairSndD (NUPPT.inArg z)))) ++ pairFstD (NUPPT.inArg z))))

/-- The output of `A'`: the `2n`-bit truncation of `y^d mod N` if the test passes, `[]` otherwise. -/
private def rsa_fOut (A : NUPPT) (z : List Bool) : List Bool :=
  if rsa_fTest A z then
    (pairSndD (pairEncode (rsa_fV A z)
      (subStr (pairEncode (List.replicate ((PolyExpr.mul (.const 2) .var).eval (NUPPT.inParam z).length) true)
          (List.replicate ((PolyExpr.mul (.const 2) .var).eval (NUPPT.inParam z).length) true)) ++
        rsa_fV A z))).drop (PolyExpr.var.eval (pairFstD (pairEncode (rsa_fV A z)
      (subStr (pairEncode (List.replicate ((PolyExpr.mul (.const 2) .var).eval (NUPPT.inParam z).length) true)
          (List.replicate ((PolyExpr.mul (.const 2) .var).eval (NUPPT.inParam z).length) true)) ++
        rsa_fV A z))).length)
  else []

/-- The string computation of `A'` is polynomial-time (`A.polyTimeComputable_output`, `H.divMod`,
`H.mul`, `H.le`, `H.sub`, `H.xgcd`, `H.modExp`, `polyTimeComputable_pairDropPoly`).

**Proof sketch.** Each word is one bundle field applied to pairs of earlier words, in applied
form (`PolyTimeComputable.comp'`) and folded into its definition: the answer of `A` on the re-laid-out input
(`NUPPT.polyTimeComputable_layout`), the cofactor (`H.divMod`), the product (`H.mul`) and the
test (two `H.le`, `polyTimeComputable_and`), `Φ` (`H.sub`, `H.mul`, a constant prefix), `d`
(`H.xgcd`), `y^d mod N` (`H.modExp`, with the zero prefix `H.sub ⟨1y, 1y⟩`), and the `2n`-bit
truncation (`polyTimeComputable_unaryPoly`, `H.sub`, `polyTimeComputable_pairDropPoly var`);
`polyTimeComputable_ite` selects the output. -/
private theorem rsa_fOut_poly (H : ArithmeticFP) (A : NUPPT) : PolyTimeComputable (rsa_fOut A) := by
  have hN : PolyTimeComputable fun z => pairFstD (NUPPT.inArg z) :=
    PolyTimeComputable.comp' polyTimeComputable_pairFstD NUPPT.polyTimeComputable_inArg
  have he : PolyTimeComputable fun z => pairFstD (pairSndD (NUPPT.inArg z)) :=
    PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
  have hy : PolyTimeComputable fun z => pairSndD (pairSndD (NUPPT.inArg z)) :=
    PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' polyTimeComputable_pairSndD NUPPT.polyTimeComputable_inArg)
  have hS : PolyTimeComputable (rsa_fS A) := by
    have h := PolyTimeComputable.comp' A.polyTimeComputable_output (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam hN NUPPT.polyTimeComputable_inAdvice NUPPT.polyTimeComputable_inCoins)
    unfold rsa_fS
    exact h
  have hQ : PolyTimeComputable (rsa_fQ A) := by
    have h := PolyTimeComputable.comp' polyTimeComputable_pairFstD (PolyTimeComputable.comp' H.divMod (hN.pairEncode hS))
    unfold rsa_fQ
    exact h
  have hM := PolyTimeComputable.comp' H.mul (hS.pairEncode hQ)
  have hT : PolyTimeComputable fun z => [rsa_fTest A z] := by
    have h := polyTimeComputable_and
      (p := fun z => decide (listToNat (mulStr (pairEncode (rsa_fS A z) (rsa_fQ A z))) ≤
        listToNat (pairFstD (NUPPT.inArg z))))
      (q := fun z => decide (listToNat (pairFstD (NUPPT.inArg z)) ≤
        listToNat (mulStr (pairEncode (rsa_fS A z) (rsa_fQ A z)))))
      (H.le_poly hM hN) (H.le_poly hN hM)
    unfold rsa_fTest
    exact h
  have hPhi : PolyTimeComputable (rsa_fPhi A) := by
    have h1 := PolyTimeComputable.comp' H.sub (hS.pairEncode (polyTimeComputable_const [true]))
    have h2 := PolyTimeComputable.comp' H.sub (hQ.pairEncode (polyTimeComputable_const [true]))
    have h0 := PolyTimeComputable.comp' H.sub ((polyTimeComputable_const [true]).pairEncode
      (polyTimeComputable_const [true]))
    have h := h0.append (PolyTimeComputable.comp' H.mul (h1.pairEncode h2))
    unfold rsa_fPhi
    exact h
  have hD : PolyTimeComputable (rsa_fD A) := by
    have h := PolyTimeComputable.comp' polyTimeComputable_pairSndD (PolyTimeComputable.comp' H.xgcd (he.pairEncode hPhi))
    unfold rsa_fD
    exact h
  have hV : PolyTimeComputable (rsa_fV A) := by
    have h1y := (polyTimeComputable_prepend [true]).comp hy
    have hz := PolyTimeComputable.comp' H.sub (h1y.pairEncode h1y)
    have h := PolyTimeComputable.comp' H.modExp (hy.pairEncode (hD.pairEncode (hz.append hN)))
    unfold rsa_fV
    exact h
  have hO := PolyTimeComputable.comp' (polyTimeComputable_unaryPoly (.mul (.const 2) .var)) NUPPT.polyTimeComputable_inParam
  have hZ := PolyTimeComputable.comp' H.sub (hO.pairEncode hO)
  have hW := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly .var) (hV.pairEncode (hZ.append hV))
  have h := polyTimeComputable_ite (p := rsa_fTest A) hT hW (polyTimeComputable_const [])
  unfold rsa_fOut
  exact h

/-- **The string computation is `A'`**: `rsa_fOut A = rsaFromFactorRaw A`.

**Proof sketch.** With `s = ⟦p'⟧`, `N`, `e`, `y` read from the input: the cofactor word reads as
`N / s` (`divModStr_pairEncode`, `N / s ≤ N`), so the test is `s (N / s) = N`; the word of `Φ`
reads as `Φ = (s − 1)(N / s − 1)` (leading zero, `listToNat_subStr`, `listToNat_mulStr`); the
word of `d` reads as `d = (e : Z_Φ)⁻¹.val` exactly (`xgcdStr_pairEncode`; `d < Φ` if `Φ ≠ 0`,
and `d ≤ 1` in `Z_0 = ℤ`, `val_inv_natCast_zmod_zero_le`); `modExpStr` at the modulus word with
`|y| + 1` leading zeros reads as `y^d mod N` exactly (`y^d mod N < N` if `N ≠ 0`; if `N = 0` then
`Φ = 0`, `d ≤ 1` and `y^d < 2^{|y| + 1}`); and the truncation is the `2n`-bit numeral
(`natToList_zero_append_drop`). -/
private theorem rsa_fOut_eq (A : NUPPT) (z : List Bool) : rsa_fOut A z = rsaFromFactorRaw A z := by
  unfold rsa_fOut rsa_fTest rsa_fV rsa_fD rsa_fPhi rsa_fQ rsaFromFactorRaw rsaFromFactorStep
  rw [show A.output (NUPPT.layout (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (NUPPT.inAdvice z)
    (NUPPT.inCoins z)) = rsa_fS A z from rfl]
  generalize rsa_fS A z = S
  generalize pairFstD (NUPPT.inArg z) = Nw
  generalize pairFstD (pairSndD (NUPPT.inArg z)) = ew
  generalize pairSndD (pairSndD (NUPPT.inArg z)) = yw
  generalize (NUPPT.inParam z).length = n
  -- the cofactor, the product and the test
  have hQ : listToNat (pairFstD (divModStr (pairEncode Nw S))) = listToNat Nw / listToNat S := by
    rw [divModStr_pairEncode, pairFstD_pairEncode,
      listToNat_natToList ((Nat.div_le_self _ _).trans_lt (listToNat_lt_two_pow Nw))]
  have hprod : listToNat (mulStr (pairEncode S (pairFstD (divModStr (pairEncode Nw S))))) =
      listToNat S * (listToNat Nw / listToNat S) := by
    rw [listToNat_mulStr, hQ]
  have htest : (decide (listToNat (mulStr (pairEncode S (pairFstD (divModStr (pairEncode Nw S))))) ≤
        listToNat Nw) && decide (listToNat Nw ≤
        listToNat (mulStr (pairEncode S (pairFstD (divModStr (pairEncode Nw S))))))) =
      decide (listToNat S * (listToNat Nw / listToNat S) = listToNat Nw) := by
    rw [hprod, Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro h
      omega
    · intro h
      omega
  rw [htest]
  by_cases hc : listToNat S * (listToNat Nw / listToNat S) = listToNat Nw
  swap
  · rw [if_neg (by simpa using hc), if_neg hc]
  rw [if_pos (by simpa using hc), if_pos hc]
  -- `Φ`, `d` and `y^d mod N` read from their words
  have hPhi : listToNat (subStr (pairEncode [true] [true]) ++
      mulStr (pairEncode (subStr (pairEncode S [true]))
        (subStr (pairEncode (pairFstD (divModStr (pairEncode Nw S))) [true])))) =
      (listToNat S - 1) * (listToNat Nw / listToNat S - 1) := by
    rw [subStr_self, listToNat_natToList_zero_append, listToNat_mulStr, listToNat_subStr,
      listToNat_subStr, listToNat_singleton_true, hQ]
  set Φw := subStr (pairEncode [true] [true]) ++
      mulStr (pairEncode (subStr (pairEncode S [true]))
        (subStr (pairEncode (pairFstD (divModStr (pairEncode Nw S))) [true]))) with hΦw
  have hΦlen : 1 ≤ Φw.length := by
    rw [hΦw, List.length_append, subStr_self, length_natToList, List.length_singleton]
    omega
  have hD : listToNat (pairSndD (xgcdStr (pairEncode ew Φw))) =
      ((listToNat ew : ZMod ((listToNat S - 1) * (listToNat Nw / listToNat S - 1)))⁻¹).val := by
    rw [xgcdStr_pairEncode, pairSndD_pairEncode, hPhi]
    apply listToNat_natToList
    by_cases hΦ : (listToNat S - 1) * (listToNat Nw / listToNat S - 1) = 0
    · rw [hΦ]
      calc _ ≤ 1 := val_inv_natCast_zmod_zero_le _
        _ < 2 ^ Φw.length := Nat.one_lt_two_pow (by omega)
    · haveI : NeZero ((listToNat S - 1) * (listToNat Nw / listToNat S - 1)) := ⟨hΦ⟩
      exact (ZMod.val_lt _).trans (hPhi ▸ listToNat_lt_two_pow Φw)
  have hNw : listToNat (subStr (pairEncode ([true] ++ yw) ([true] ++ yw)) ++ Nw) = listToNat Nw := by
    rw [subStr_self, listToNat_natToList_zero_append]
  have hV : listToNat (modExpStr (pairEncode yw (pairEncode (pairSndD (xgcdStr (pairEncode ew Φw)))
      (subStr (pairEncode ([true] ++ yw) ([true] ++ yw)) ++ Nw)))) =
      listToNat yw ^ ((listToNat ew : ZMod ((listToNat S - 1) *
        (listToNat Nw / listToNat S - 1)))⁻¹).val % listToNat Nw := by
    rw [modExpStr_pairEncode, hD, hNw]
    apply listToNat_natToList
    rw [List.length_append, subStr_self, length_natToList, List.length_append,
      List.length_singleton]
    rcases Nat.eq_zero_or_pos (listToNat Nw) with h0 | h0
    · -- `N = 0`: then `Φ = 0`, `d ≤ 1` and `y^d ≤ max 1 y < 2^{|y| + 1}`
      have hΦ : (listToNat S - 1) * (listToNat Nw / listToNat S - 1) = 0 := by
        rw [h0, Nat.zero_div, Nat.zero_sub, mul_zero]
      rw [hΦ, h0, Nat.mod_zero]
      have hd := val_inv_natCast_zmod_zero_le (listToNat ew)
      have hyl := listToNat_lt_two_pow yw
      have h2 : 2 ^ (1 + yw.length) ≤ 2 ^ (1 + yw.length + Nw.length) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : 2 ^ (1 + yw.length) = 2 * 2 ^ yw.length := by rw [pow_add, pow_one]
      interval_cases h : ((listToNat ew : ZMod 0)⁻¹).val
      · rw [pow_zero]
        have := Nat.one_le_two_pow (n := yw.length)
        omega
      · rw [pow_one]
        omega
    · calc _ < listToNat Nw := Nat.mod_lt _ h0
        _ < 2 ^ Nw.length := listToNat_lt_two_pow Nw
        _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pairSndD_pairEncode, pairFstD_pairEncode, PolyExpr.eval_var,
    subStr_self (List.replicate _ true), List.length_replicate, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    natToList_zero_append_drop, hV]

/-- **`A'` is polynomial-time** [PS10, Theorem 55.2, "the running time of `A'` is essentially
the running time of `A` plus `O(log³ n)`"] given the arithmetic bundle.

**Proof sketch.** Compute `A'` word by word (`rsa_fOut_poly`), each word one bundle field:
`p'` is `A.output` on the re-paired layout (`NUPPT.polyTimeComputable_layout`,
`A.polyTimeComputable_output`); `q'` is the quotient of `H.divMod ⟨N, p'⟩`; the test `p' q' = N`
is `H.mul` and two `H.le` comparisons, since the widths of `p' q'` and `N` differ
(`polyTimeComputable_and`); `Φ = (p' − 1)(q' − 1)` is two decrements `H.sub` with `[true]`
(run-3 audit P7-1) and `H.mul`, behind one leading zero; `d` is the second component of
`xgcdStr ⟨e, Φ⟩` (`H.xgcd`); `y^d mod N` is `H.modExp` with `|y| + 1` leading zeros before
`N` (the zeros are `H.sub ⟨1y, 1y⟩`). The two zero prefixes make every word read exactly, also on
the degenerate inputs `Φ = 0` (where `d ≤ 1`) and `N = 0` (where `y^d mod N = y^d`). The
`2n`-bit output is the truncation `(⟦0⟧_{2n} ++ v).drop |v|` of the value word `v`
(`H.sub ⟨1^{2n}, 1^{2n}⟩`, `polyTimeComputable_pairDropPoly var`), and `polyTimeComputable_ite`
selects it or `[]` by the test. The word computation equals `rsaFromFactorRaw A`
(`rsa_fOut_eq`: `divModStr_pairEncode`, `xgcdStr_pairEncode`, `modExpStr_pairEncode`,
`listToNat_subStr`, `natToList_zero_append_drop`). -/
theorem polyTimeComputable_rsaFromFactorRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (rsaFromFactorRaw A) := by
  have h := rsa_fOut_poly H A
  rw [show rsa_fOut A = rsaFromFactorRaw A from funext (rsa_fOut_eq A)] at h
  exact h

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
  rw [factorProb_eq, uprob_prod]
  unfold rsaProb
  apply OneWay.uexp_mono
  intro z
  set φ := rsaFromFactorer_coinsEquiv H A n
  -- reorder the coordinates: `(ω, (e, y)) ↦ (e, (y, φ⁻¹ ω))`
  let E : A.Coins n × ((ZMod (Nat.totient (z.p * z.q)))ˣ × (ZMod (z.p * z.q))ˣ) ≃
      (ZMod (Nat.totient (z.p * z.q)))ˣ × ((ZMod (z.p * z.q))ˣ × (rsaFromFactorer H A).Coins n) :=
    (Equiv.prodComm _ _).trans ((Equiv.prodAssoc _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) φ.symm)))
  refine le_of_le_of_eq ?_ (uprob_comp_equiv E _)
  rw [← uprob_fst (β := (ZMod (Nat.totient (z.p * z.q)))ˣ × (ZMod (z.p * z.q))ˣ)]
  apply uprob_mono
  rintro ⟨ω, eU, y⟩ ⟨x, hx, hpq⟩
  rw [NUPPT.inverter_eq_some_iff] at hx
  have hs : listToNat (A.runAt n (natToList (2 * n) (z.p * z.q)) ω) = z.p ∨
      listToNat (A.runAt n (natToList (2 * n) (z.p * z.q)) ω) = z.q := by
    rw [natToList_eq, ← modulusBits_eq, hx, ← bitsToNat_eq_listToNat]
    exact hpq
  have he : (eU : ZMod (Nat.totient (z.p * z.q))).val < 2 ^ (2 * n) :=
    (ZMod.val_lt _).trans ((Nat.totient_le _).trans_lt z.mul_lt)
  have hy : (y : ZMod (z.p * z.q)).val < 2 ^ (2 * n) := (ZMod.val_lt _).trans z.mul_lt
  show ∃ x : Fin (2 * n) → Bool, decodeFin (2 * n) ((rsaFromFactorer H A).runAt n
      (rsaInput n z eU y) (φ.symm ω)) = some x ∧
    ((bitsToNat x : ℕ) : ZMod (z.p * z.q)) ^ (eU : ZMod (Nat.totient (z.p * z.q))).val =
      (y : ZMod (z.p * z.q))
  rw [rsaInput, rsaFromFactorer_runAt, Equiv.apply_symm_apply, listToNat_natToList z.mul_lt,
    listToNat_natToList he, listToNat_natToList hy]
  exact rsaFromFactorStep_correct z hs (ZMod.val_coe_unit_coprime eU) y

/-- **Theorem 55.2** [PS10, Theorem 55.2]: the RSA assumption implies the factoring
assumption (under the arithmetic hypotheses).

**Deviation:** both assumptions on uniform pairs of distinct primes of `Π_n`
(module docstring); the text's `n`/`k` mix-up is resolved as `n`.

**Proof sketch.** For every `A`, `factorProb A n ≤ rsaProb (rsaFromFactorer H A) n`
(`factorProb_le_rsaProb`), which is negligible by `hR`; conclude by `Negligible.mono`
(`factorProb_nonneg`). -/
theorem rsa_imp_factoring (H : ArithmeticFP) (hR : RSAAssumption) : FactoringAssumption := by
  refine factoringAssumption_iff.2 fun A =>
    (rsaAssumption_iff.1 hR (rsaFromFactorer H A)).mono ⟨0, fun n _ => ?_⟩
  rw [abs_of_nonneg (factorProb_nonneg A n), abs_of_nonneg (rsaProb_nonneg _ n)]
  exact factorProb_le_rsaProb H A n

end TCSlib.Cryptography.Candidates
