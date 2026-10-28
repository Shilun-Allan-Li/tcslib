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

/-- The RSA probability is nonnegative. -/
theorem rsaProb_nonneg (A : NUPPT) (n : ℕ) : 0 ≤ rsaProb A n := by
  unfold rsaProb uexp
  exact div_nonneg (Finset.sum_nonneg fun z _ => uprob_nonneg _) (Nat.cast_nonneg _)

/-- The RSA probability is at most one. -/
theorem rsaProb_le_one (A : NUPPT) (n : ℕ) : rsaProb A n ≤ 1 := by
  rcases isEmpty_or_nonempty (DistinctPrimes n) with h | h
  · unfold rsaProb uexp
    simp
  · unfold rsaProb
    exact (OneWay.uexp_mono fun z => uprob_le_one _).trans (OneWay.uexp_const 1).le

/-- At the degenerate parameters `n < 2` the RSA experiment is empty. -/
theorem rsaProb_eq_zero_of_lt (A : NUPPT) {n : ℕ} (hn : n < 2) : rsaProb A n = 0 := by
  haveI := DistinctPrimes.isEmpty_of_lt hn
  unfold rsaProb uexp
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

/-! ## The generator, the domain sampler and the inverter -/

/-- The width `B(n) = 2(n + 2)` of a coin block of the rejection samplers (at least the bit
length of any modulus `N < 2^{2 max(n,2)}`). -/
def rsaBlock : PolyExpr := .mul (.const 2) (.add .var (.const 2))

/-- The number of trials `T(n) = (4n + 8) n` of the rejection samplers: with acceptance rate
at least `1/(2 ⌈log₂ N⌉) ≥ 1/(4n + 8)` per trial (`NumberTheory.le_totient_mul_log_succ`,
C9), the failure probability is at most `e^{-n}` (`one_sub_one_div_pow_le_exp_neg`). -/
def rsaTrials : PolyExpr := .mul (.add (.mul (.const 4) .var) (.const 8)) .var

/-- The coins of the domain sampler: `T(n)` blocks of `B(n)` bits. -/
def rsaSampleCoins : PolyExpr := .mul rsaTrials rsaBlock

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

/-- A sampled value is below `N` and coprime to `N`. -/
theorem sampleUnitL_spec {N k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleUnitL N k B T r = some v) :
    v < N ∧ Nat.Coprime v N :=
  (rejectBlocksL_spec h).1

/-- The string function of the domain sampler on the modulus numeral `w` at parameter `n`
with coins `r`: a unit modulo `N = listToNat w` by rejection (`sampleUnitL` with the bit
length `Nat.size N` of `N`), written as a numeral of the width of `w`; the fallback `1 mod N`
on failure. -/
def unitSampleStr (w : List Bool) (n : ℕ) (r : List Bool) : List Bool :=
  natToList w.length
    ((sampleUnitL (listToNat w) (Nat.size (listToNat w)) (rsaBlock.eval n) (rsaTrials.eval n) r).getD
      (1 % listToNat w))

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

/-- **The generator is polynomial-time** [PS10, Theorem 53.2, "the set `I` is easy to
sample"] given the arithmetic bundle.

**Proof sketch.** Cut the coins at the unary lengths `1^{2m³}` (`polyTimeComputable_pairTakePoly`
/`_pairDropPoly samplePrimeCoins` on `⟨1^m, r⟩`, with `1^m = 1^{max n 2}` by
`polyTimeComputable_unaryPoly`); each prime is the `iterateFind` loop of
`NumberTheory.exists_samplePrime_nuppt` with the test `H.prime`; the validity test is two
`H.prime` calls, a `pairEq` test and two `H.le` comparisons with `1^m`, the fallback a
constant (`polyTimeComputable_ite`; the fallback prime `2` of a failed `samplePrimeL` run is a
constant numeral, P7-7); `N` is `H.mul`; `Φ(N) = (p−1)(q−1)` by two decrements `H.sub` on
`⟨p, [true]⟩`, `⟨q, [true]⟩` (`listToNat_subStr`) and `H.mul`; the unary bit length
`1^{Nat.size Φ}` is `H.size` (run-3 audit P7-1); the rejection loop (`sampleUnitL =
rejectBlocksL`) is `polyTimeComputable_iterateFind` over the blocks of `1^{B(m)}` bits, each
trial reading `Nat.size Φ` bits (`polyTimeComputable_pairTakePoly var` on
`⟨1^{Nat.size Φ}, block⟩`) with the tests `H.le` and `H.xgcd` (`gcd = 1`), and `d` is the
second component of `xgcdStr ⟨e, Φ⟩`; pair the numerals. -/
theorem polyTimeComputable_rsaGenRaw (H : ArithmeticFP) : PolyTimeComputable rsaGenRaw := by
  sorry

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
  simp [rsaGenRaw, NUPPT.inParam, NUPPT.inCoins, NUPPT.advInput]

/-- The string function of the domain sampler on the raw layout `⟨⟨⟨1^n, ⟨N, e⟩⟩, α⟩, r⟩`:
`unitSampleStr` on the modulus numeral. -/
def rsaSampleRaw (z : List Bool) : List Bool :=
  unitSampleStr (pairFstD (NUPPT.inArg z)) (NUPPT.inParam z).length (NUPPT.inCoins z)

/-- **The unit sampler is polynomial-time** [PS10, Theorem 53.2, "the set `D_i` is also
easy to sample"]: for any polynomial-time projection `f` of the raw input to the modulus
numeral, `z ↦ unitSampleStr (f z) n (coins z)` is polynomial-time (shared by the RSA and
Rabin samplers).

**Proof sketch.** The unary bit length `1^{Nat.size N}` of `N = f z` is `H.size` (run-3
audit P7-1); the trial loop (`sampleUnitL = rejectBlocksL`) is
`polyTimeComputable_iterateFind` over the blocks of `1^{B(n)}` bits
(`polyTimeComputable_pairDropPoly`), each trial reading the first `k` bits
(`polyTimeComputable_pairTakePoly var` on `⟨1^k, block⟩`), comparing them with `N` (`H.le`)
and testing `gcd = 1` (`H.xgcd`, `pairEq` with `[true]`); the output is padded to the width
of the numeral (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). -/
theorem polyTimeComputable_unitSampleStr (H : ArithmeticFP) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) :
    PolyTimeComputable fun z => unitSampleStr (f z) (NUPPT.inParam z).length (NUPPT.inCoins z) := by
  sorry

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
  simp [rsaInvRaw, NUPPT.inArg, NUPPT.advInput]

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
  sorry

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

/-- **The RSA collection** [PS10, Theorem 53.2]: the collection underlying `rsaTrapdoor`. -/
noncomputable def rsaCollection (H : ArithmeticFP) : Collection := (rsaTrapdoor H).toCollection

/-- The index generated by the RSA collection is `⟨N, e⟩` of `rsaGenParams`. -/
theorem rsaCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rsaCollection H).gen.Coins n) :
    (rsaCollection H).index n r = rsaIndexOf _ (rsaGenParams n (List.ofFn r)) := by
  show pairFstD ((rsaGen H).runAt n [] r) = _
  rw [rsaGen_runAt, rsaGenOut, pairFstD_pairEncode]

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
  sorry

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
@[simp] theorem coins_rsaBreaker (A : NUPPT) : (rsaBreaker A).coins = A.coins := rfl

/-- The activation of `rsaBreaker`: `A'(1^n, ⟨N, ⟨e, y⟩⟩; r) = A(1^n, ⟨⟨N, e⟩, y⟩; r)`. -/
theorem rsaBreaker_runAt (A : NUPPT) (n : ℕ) (N e y : List Bool) (r : (rsaBreaker A).Coins n) :
    (rsaBreaker A).runAt n (pairEncode N (pairEncode e y)) r =
      A.runAt n (pairEncode (pairEncode N e) y) r := by
  rw [NUPPT.runAt_eq]
  unfold rsaBreaker
  rw [NUPPT.runAtL_ofPolyTime]
  simp [NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.inCoins,
    NUPPT.advInput]

/-- **Inverting the RSA collection breaks the RSA assumption** [PS10, proof of Theorem 53.2]:
for `n ≥ 2`, the inversion probability of `A` against the RSA collection is at most the RSA
probability of `rsaBreaker A` plus the statistical error of the generator.

**Proof sketch.** At a generated index `⟨N, e⟩` (`rsaCollection_index`, valid), the domain
is `Z_N^*` (`rsaMod_indexOf`), `f_{N,e}(x)` is the numeral of `(x^e).val` (`rsaF_perm`,
`rsaEnc`), and a decoded answer `x'` with `f x' = f x` has `x' = x` (`PermCollection.f_injective`),
so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", which implies the RSA
event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`, `decodeFin_ofFn`,
`bitsToNat_natToBits`, `val_units_pow`). Since `x ↦ x^e` pushes uniform to uniform
(`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the inner probability equals the RSA
inner probability at `(z, e)`. The law of `(z, e)` under the generator's coins is within
`rsaGenErr n` of the ideal uniform law on `DistinctPrimes n × Z*_{Φ(N)}`
(`statClose_samplePrime` with the prime fallback `natToBits n 2` of `samplePrimeL` — run-3
audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map` through the validity
test with `uprob_diag` and `one_div_card_primes_le` for the fallback on `p = q`,
`statClose_rejectBlocksL` for `e` with the acceptance rate of the sampleClose sketch); `StatClose.abs_uprob_sub_le_prod` with the
auxiliary coins `(y, r)` turns `uexp` over the generator's coins into `uexp` over `z`
(`uexp_prod`, `uprob_prod`) up to `rsaGenErr n`. -/
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
  · rw [rsaFromFactorStep, if_pos hpq.1, natToList]
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
    (rsaFromFactorer H A).coins = A.coins := rfl

/-- The activation of `A'`: `A'(1^n, ⟨N, ⟨e, y⟩⟩; r) = rsaFromFactorStep n (A(1^n, N; r)) N e y`. -/
theorem rsaFromFactorer_runAt (H : ArithmeticFP) (A : NUPPT) (n : ℕ) (N e y : List Bool)
    (r : (rsaFromFactorer H A).Coins n) :
    (rsaFromFactorer H A).runAt n (pairEncode N (pairEncode e y)) r =
      rsaFromFactorStep n (A.runAt n N r) (listToNat N) (listToNat e) (listToNat y) := by
  rw [NUPPT.runAt_eq]
  unfold rsaFromFactorer
  rw [NUPPT.runAtL_ofPolyTime]
  simp [rsaFromFactorRaw, NUPPT.runAt, NUPPT.layout, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice,
    NUPPT.inCoins, NUPPT.advInput]

/-- **A factorer gives an RSA breaker with the same probability** [PS10, proof of
Theorem 55.2]: `Pr[A factors N] ≤ Pr[A' breaks RSA]`.

**Proof sketch.** `rsaProb` averages over `z` the probability over `(e, y, r)`; for fixed
`z` and `r`, if `A(1^n, N; r)` reads as `p` or `q` then `A'` succeeds for *every* `(e, y)`
(`rsaFromFactorer_runAt`, `rsaFromFactorStep_correct`, `rsaInput`,
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
