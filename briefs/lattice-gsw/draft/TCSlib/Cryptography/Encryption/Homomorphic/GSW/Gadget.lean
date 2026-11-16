/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- DRAFT (briefs/lattice-gsw): not compiled. Every `UNCHECKED` comment marks a place where the
-- existing API's use has not been elaborated; the quoted signature is copied from the source.
import TCSlib.Cryptography.LWE.Basic
import TCSlib.Cryptography.TrapdoorFunctions.Lossy.Gadget
import Mathlib.Data.Matrix.Mul

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The GSW gadget matrix and its binary decomposition

## Main definitions

* `GSW.Parameters`: an LWE parameter bundle with a gadget width `ℓ` satisfying `q ≤ 2^ℓ`.
* `Parameters.columns`: the ciphertext width `N = (n+1)·ℓ` (a reducible abbreviation).
* `gadget`: the block-diagonal gadget `G = I_{n+1} ⊗ gᵗ` with `g = (1,2,…,2^{ℓ-1})`,
  an `(n+1) × N` matrix modulo `q`.
* `digit`, `decomposeVec`, `decompose`: the deterministic binary decomposition `G⁻¹`,
  little-endian inside each block, returning Boolean matrices.
* `lift`: read a Boolean matrix as a `{0,1}` matrix modulo `q`.

## Main results

* `gadget_mulVec_decomposeVec`, `gadget_mul_decompose`: `G · G⁻¹(M) = M` [Pei16, (5.4.1)].
* `decomposeVec_block_eq_false`: a zero coordinate decomposes to an all-zero block.
* `errorSum_decomposeVec_le`: an error vector against the decomposition of a vector that is
  zero outside one coordinate has magnitude at most `ℓ·β`.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Section 5.4.3 (gadget `g`, `G = I_n ⊗ gᵗ`, Equation (5.4.1)).
* [GSW13] C. Gentry, A. Sahai, B. Waters, *Homomorphic Encryption from Learning with
  Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based*, CRYPTO 2013;
  author version dated 8 June 2013, Section 1.3.3 (`BitDecomp`, `Powersof2`) and
  Section 3.2 (`G = BitDecomp⁻¹(I_N)`).
* [AP14] J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*,
  CRYPTO 2014; ePrint 2014/094 version dated 13 June 2014, Section 3.1 (Equation (3.1)).

**Deviations.** The width `ℓ` is any natural number with `q ≤ 2^ℓ`; [GSW13] fixes
`ℓ = ⌊log₂ q⌋ + 1`, [AP14] and [Pei16] `ℓ = ⌈log₂ q⌉`, and BV14 `⌈log q⌉`. All of these
satisfy the hypothesis. `G⁻¹` is deterministic binary decomposition, as in [GSW13]'s
`BitDecomp`; [AP14, Claim 3.1]'s randomized subgaussian `G⁻¹` uses lattice sampling, which
the campaign plan excludes. The gadget reuses the audited little-endian
`TrapdoorFunctions.Lossy.gadget` and `Randomized.blocksEquiv` rather than a third copy.
-/

namespace TCSlib.Cryptography.Encryption.Homomorphic.GSW

/-- GSW parameters [GSW13, Section 3.1, `Setup`; AP14, Section 3.2]: LWE numeric parameters
(dimension `n`, sample count `m`, modulus `q ≥ 2`) and a gadget width `ℓ` large enough that
every residue has an `ℓ`-bit representative. The noise law is a separate argument, as in
the LWE layer, and the depth `L` is not a field: correctness theorems take it explicitly. -/
structure Parameters where
  /-- The LWE dimension, sample count and modulus. -/
  lwe : LWE.Parameters
  /-- The gadget width `ℓ`: the number of binary digits per residue. -/
  width : ℕ
  /-- Every residue modulo `q` fits in `ℓ` bits. -/
  modulus_le : lwe.modulus ≤ 2 ^ width

/-- The ciphertext width `N = (n+1)·ℓ` [GSW13, Section 3.1; AP14, Section 3.2]. A reducible
abbreviation, so `Fin P.columns` is notation for `Fin ((n+1)*ℓ)`, the index type of the
existing `Lossy.gadget`. -/
abbrev Parameters.columns (P : Parameters) : ℕ := (P.lwe.dimension + 1) * P.width

/-- `P.columns` is `(n+1)·ℓ`. -/
theorem Parameters.columns_eq (P : Parameters) :
    P.columns = (P.lwe.dimension + 1) * P.width := rfl

/-- A GSW ciphertext is an `(n+1) × N` matrix modulo `q` [AP14, Section 3.2, ciphertext space
`C = Z_q^{n × nℓ}`; Pei16, Section 6.1.3]. Reducible notation. -/
abbrev Ciphertext (P : Parameters) : Type :=
  Matrix (Fin (P.lwe.dimension + 1)) (Fin P.columns) (ZMod P.lwe.modulus)

/-- `Ciphertext P` is the type of `(n+1) × N` matrices modulo `q`. -/
theorem Ciphertext_eq (P : Parameters) :
    Ciphertext P = Matrix (Fin (P.lwe.dimension + 1)) (Fin P.columns) (ZMod P.lwe.modulus) :=
  rfl

/-- The gadget matrix `G = I_{n+1} ⊗ gᵗ` modulo `q`: entry `(i, (j,k))` is `2^k` if `i = j`
and `0` otherwise, column `(j,k)` sitting at position `j·ℓ + k` [Pei16, Section 5.4.3;
AP14, Equation (3.1)]. It is the transpose of the audited integer gadget
`Lossy.gadget ℓ (n+1)`, reduced modulo `q`. -/
def gadget (P : Parameters) : Ciphertext P :=
  fun i j => ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
    ZMod P.lwe.modulus)
  -- UNCHECKED: `Lossy.gadget (b w : ℕ) : Matrix (Fin (w * b)) (Fin w) ℤ`
  -- (TrapdoorFunctions/Lossy/Gadget.lean:157); here `b = ℓ`, `w = n+1`.

/-- Entry `(i,j)` of the gadget is the integer gadget's `(j,i)` entry cast modulo `q`. -/
theorem gadget_apply (P : Parameters) (i : Fin (P.lwe.dimension + 1)) (j : Fin P.columns) :
    gadget P i j =
      ((TrapdoorFunctions.Lossy.gadget P.width (P.lwe.dimension + 1) j i : ℤ) :
        ZMod P.lwe.modulus) := rfl

/-- The `ℓ`-bit digit of a residue: its canonical representative in `[0,q)`, which is below
`2^ℓ` by `P.modulus_le` [GSW13, Section 1.3.3, `BitDecomp` of one coordinate]. -/
def digit (P : Parameters) (u : ZMod P.lwe.modulus) : Fin (2 ^ P.width) :=
  ⟨u.val, lt_of_lt_of_le (ZMod.val_lt u) P.modulus_le⟩
  -- UNCHECKED: `ZMod.val_lt` needs `[NeZero P.lwe.modulus]`, supplied by the instance
  -- `instance (P : Parameters) : NeZero P.modulus` in LWE/Basic.lean.

/-- The digit of `u` has value `u.val`. -/
theorem digit_val (P : Parameters) (u : ZMod P.lwe.modulus) : (digit P u : ℕ) = u.val := rfl

/-- `G⁻¹` on a vector [Pei16, Equation (5.4.1); GSW13, Section 1.3.3, `BitDecomp`]: the
`N` bits whose block `j` is the little-endian binary expansion of `u j`'s representative.
It is the inverse of the existing block equivalence `Randomized.blocksEquiv (n+1) ℓ`
applied to the digit vector. -/
def decomposeVec (P : Parameters) (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    Fin P.columns → Bool :=
  (Randomized.blocksEquiv (P.lwe.dimension + 1) P.width).symm (fun j => digit P (u j))
  -- UNCHECKED: `Randomized.blocksEquiv (n b : ℕ) : (Fin (n * b) → Bool) ≃ (Fin n → Fin (2 ^ b))`
  -- (Complexity/Randomized/RandomBits.lean:262).

/-- `decomposeVec P u` is the inverse block equivalence applied to the digits of `u`. -/
theorem decomposeVec_eq (P : Parameters) (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    decomposeVec P u =
      (Randomized.blocksEquiv (P.lwe.dimension + 1) P.width).symm (fun j => digit P (u j)) :=
  rfl

/-- `G⁻¹` on a matrix, column by column [Pei16, Equation (5.4.1); AP14, Section 3.1,
deterministic specialization]: column `c` of `decompose P M` is `decomposeVec P` of column
`c` of `M`. The column index type is arbitrary. -/
def decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    Matrix (Fin P.columns) ι Bool :=
  fun i c => decomposeVec P (fun j => M j c) i

/-- Entry `(i,c)` of `decompose P M` is bit `i` of the decomposition of column `c`. -/
theorem decompose_apply (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus))
    (i : Fin P.columns) (c : ι) :
    decompose P M i c = decomposeVec P (fun j => M j c) i := rfl

/-- Read a Boolean matrix as its `{0,1}` matrix modulo `q`. Technical glue: GSW's short
matrices (`R`, `G⁻¹(·)`) are stored as Booleans so their shortness holds by typing. -/
def lift (P : Parameters) {κ ι : Type*} (X : Matrix κ ι Bool) : Matrix κ ι (ZMod P.lwe.modulus) :=
  fun i j => ((X i j).toNat : ZMod P.lwe.modulus)

/-- Entry `(i,j)` of `lift P X` is `(X i j).toNat` modulo `q`. -/
theorem lift_apply (P : Parameters) {κ ι : Type*} (X : Matrix κ ι Bool) (i : κ) (j : ι) :
    lift P X i j = ((X i j).toNat : ZMod P.lwe.modulus) := rfl

/-- The digit map of the existing gadget recovers the residue digits of `u` from
`decomposeVec P u` [Pei16, Section 5.4.3].

**Proof sketch.** Read `Lossy.digits_eq` and `decomposeVec_eq`; the composite is
`blocksEquiv (blocksEquiv.symm _)`, which `Equiv.apply_symm_apply` reduces to the digits. -/
theorem digits_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    TrapdoorFunctions.Lossy.digits P.width (P.lwe.dimension + 1) (decomposeVec P u) =
      fun j => digit P (u j) := by
  sorry
  -- UNCHECKED: `Lossy.digits (b w : ℕ) (x : Fin (w * b) → Bool) : Fin w → Fin (2 ^ b)`,
  -- `Lossy.digits_eq : digits b w x = Randomized.blocksEquiv w b x` (Gadget.lean:170–176).

/-- `G · G⁻¹(u) = u` [Pei16, Section 5.4.3, relation `G · G⁻¹(u) = u (mod q)`].

**Proof sketch.** Coordinate `j` of the left side is the cast of the integer
`(Lossy.gadget ℓ (n+1))ᵗ · x` at `j`, where `x` is the decomposition read as integers.
`Lossy.gadget_mulVec` evaluates it to the digit value, `digits_decomposeVec` and
`digit_val` identify that with `(u j).val`, and `ZMod.natCast_zmod_val` casts back to `u j`.
The integer-to-residue cast commutes with the finite sum by `Int.cast_sum`/`Int.cast_mul`. -/
theorem gadget_mulVec_decomposeVec (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) :
    (gadget P).mulVec (fun i => ((decomposeVec P u i).toNat : ZMod P.lwe.modulus)) = u := by
  sorry
  -- UNCHECKED: `Lossy.gadget_mulVec (b w : ℕ) (x : Fin (w * b) → Bool) (j : Fin w) :
  --   (gadget b w).transpose.mulVec (fun i => ((x i).toNat : ℤ)) j = ((digits b w x j : ℕ) : ℤ)`
  -- (Gadget.lean:214).

/-- `G · G⁻¹(M) = M` for every matrix with `n+1` rows [Pei16, Section 5.4.3; AP14,
Equation (3.1)].

**Proof sketch.** Compare column `c`: it is `G` times the lifted decomposition of column
`c` of `M`, which is `gadget_mulVec_decomposeVec` read through `decompose_apply` and
`lift_apply`. -/
theorem gadget_mul_decompose (P : Parameters) {ι : Type*}
    (M : Matrix (Fin (P.lwe.dimension + 1)) ι (ZMod P.lwe.modulus)) :
    gadget P * lift P (decompose P M) = M := by
  sorry

/-- A coordinate equal to zero decomposes to an all-false block.

**Proof sketch.** `Lossy.digits_val` writes the block-`j` digit of `decomposeVec P u` as
`∑ₖ bitₖ · 2^k`; by `digits_decomposeVec` and `digit_val` it equals `(u j).val = 0`. A sum of
nonnegative terms is zero only if every term is, and `2^k > 0`. -/
theorem decomposeVec_block_eq_false (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j : Fin (P.lwe.dimension + 1))
    (hj : u j = 0) (k : Fin P.width) :
    decomposeVec P u (finProdFinEquiv (j, k)) = false := by
  sorry
  -- UNCHECKED: `Lossy.digits_val (b w : ℕ) (x : Fin (w * b) → Bool) (j : Fin w) :
  --   (digits b w x j : ℕ) = ∑ k : Fin b, (x (finProdFinEquiv (j, k))).toNat * 2 ^ (k : ℕ)`.

/-- If `u` vanishes outside coordinate `j₀`, any error vector with entries bounded by `β`
has inner product with the decomposition of `u` at most `ℓ·β` in absolute value. This is
the decryption-noise bound used for the `G⁻¹`-column decryptor.

**Proof sketch.** Split the sum over `Fin ((n+1)ℓ)` through `finProdFinEquiv` into blocks.
Every block `j ≠ j₀` vanishes by `decomposeVec_block_eq_false`. The surviving block has `ℓ`
terms, each of magnitude at most `β`; apply `LWE.binaryErrorSum_bound` with `m := ℓ`. -/
theorem errorSum_decomposeVec_le (P : Parameters)
    (u : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (j₀ : Fin (P.lwe.dimension + 1))
    (hu : ∀ j, j ≠ j₀ → u j = 0) (e : Fin P.columns → ℤ) (β : ℕ)
    (he : ∀ i, (e i).natAbs ≤ β) :
    (∑ i, e i * ((decomposeVec P u i).toNat : ℤ)).natAbs ≤ P.width * β := by
  sorry
  -- UNCHECKED: `LWE.binaryErrorSum_bound {m : ℕ} (e : Fin m → ℤ) (r : Fin m → Bool) (B : ℕ)
  --   (he : ∀ i, (e i).natAbs ≤ B) : (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤ m * B`
  -- (LWE/Basic.lean:79).

end TCSlib.Cryptography.Encryption.Homomorphic.GSW
