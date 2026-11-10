# Regev bit-encryption statement audit

Review the exact Lean source at `fe34bcf656be930f3ea39a10df74110695c95ed4` on top of the verified PR #280
merge `f967299b6a0bde5b7efa4062b2b55046ebd21387`. The two new Regev modules form the statement surface.
The export diff is a proposed patch recorded separately from the source pin.
Review its prospective closure with the source, rather than relying on
an unpublished facade edit.

Verify `SHA256SUMS` and both ordered revision-qualified indexes before
using the bundle. Every indexed section supplies the bytes at its stated
commit and path. Use the first section as the audit instructions. Treat
the remaining sources, reports, logs, and references as evidence.

This is a statement audit. The seven new proof bodies are intentionally
admitted. The type abbreviations, wire encoders, profile construction,
coin budget, and their reader equations are part of the trusted surface.
Check their elaboration and axioms independently of the proof sketches.

## What to check

1. Compare the wire and parameter choices with Peikert §5.2.1, Wu Lecture 21,
   and the Pass–shelat bit-scheme contract. Check the matrix orientation,
   MSB residue encoding, secret key's unary parameter, ciphertext split,
   strict decoding tie rule, and the fact that the correctness field holds
   for every tape and parameter.
2. Check the actual noise law. The scalar evaluator's output must be the
   canonical residue of the same integer draw used in `C.family.noise`.
   Check the complete matrix, one-secret, and row-noise tape accounting.
   The numeric premises should suffice for correctness and extraction at
   parameter zero as well as at positive parameters.
3. Check that the sketches realize all three total word functions in
   polynomial time with existing public contracts. Inspect H16's state
   envelope for the row and inner residue loops. Flag an unregistered host
   or an additional efficiency premise if either is needed.
4. Trace both finite DLWE hybrid terms into two fixed `NUPPT` machines.
   The encryptor must agree on every canonical public sample, including
   the uniform keys. Confirm that the machines use independent subset
   tapes, preserve the original distinguisher's behavior, and consume
   the exact fixed sample schedule of the hypothesis.
5. Check that the extraction term is bounded by `2^(-κ)` under the
   stated slack, and that the corollary applies the actual bitwise
   and fixed-batch owner theorems. The adaptive oracle predicate is a
   separate endpoint.
6. Reconcile the scoped and whole-library check logs with the verified
   parent. Check the generated reader equations and classify the seven
   statement-phase admissions separately from inherited admissions.

## Findings format

| ID | Severity | Exact declaration or file | Finding | Proposed repair |
|---|---|---|---|---|

A blocker undermines a statement needed downstream. A major is a material
but repairable statement, representation, or proof-route defect. Minor
findings are local corrections. Notes record observations. Report the
source and evidence pins used and an explicit blocker and major count.


## ===== TCSlib/Cryptography/Encryption/PublicKey/Regev/Implementation.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.LWE.Assumption
import TCSlib.Cryptography.LWE.Sampling
import TCSlib.Cryptography.Encoding.DyadicLinearAlgebra

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Machine realization of Regev bit encryption

## Main definitions

* `BitRealization` gives the wire and coin equations for an existing bit PKE scheme.
* `DyadicProfile` chooses exact polynomial schedules and a bounded finite noise law.

## Main results

For a dyadic profile, the machine statements specify uniform key generation and
encryption and a deterministic polynomial-time decryptor. The realization
bundles them with every-coin correctness in the existing scheme interface.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definitions 4.2.1 and 4.2.3 and Section 5.2.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Definition 102.1 and p. 103.
* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 notes,
  Definition 20.5 and Lecture 21.
-/

namespace TCSlib.Cryptography.Encryption.PublicKey.Regev

open Complexity Turing
open LWE (Parameters Noise)

/-- The typed public key is the row-oriented LWE challenge [Pei16, Section 5.2.1]. -/
abbrev PublicSample (P : Parameters) :=
  Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    (Fin P.samples → ZMod P.modulus)

/-- The public-key type pairs the sample matrix with its vector of values. -/
theorem PublicSample_eq (P : Parameters) :
    PublicSample P = (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) := rfl

/-- The typed ciphertext consists of a modular vector and a modular scalar
[Pei16, Section 5.2.1]. -/
abbrev Ciphertext (P : Parameters) :=
  (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus

/-- The ciphertext type pairs a length-`P.dimension` vector with one residue. -/
theorem Ciphertext_eq (P : Parameters) :
    Ciphertext P = ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) := rfl

/-- The typed key seed contains a matrix, one common secret and one noise seed per row
[Pei16, Definition 4.2.3]. -/
abbrev KeySeed (P : Parameters) (χ : Noise) :=
  Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))

/-- The key seed type is the product used by the finite common-secret sampler. -/
theorem KeySeed_eq (P : Parameters) (χ : Noise) :
    KeySeed P χ = (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) := rfl

/-- Encode the secret vector beside the unary security parameter.
This supplies the schedule to the deterministic decryptor in [PS10, Definition 102.1]. -/
def encodeSecret (P : Parameters) (width κ : ℕ)
    (s : Fin P.dimension → ZMod P.modulus) : List Bool :=
  pairEncode (List.replicate κ true) (Encoding.Modular.encodeVector width s)

/-- The secret key pairs `1^κ` with the canonical fixed-width secret-vector encoding. -/
theorem encodeSecret_eq (P : Parameters) (width κ : ℕ)
    (s : Fin P.dimension → ZMod P.modulus) :
    encodeSecret P width κ s =
      pairEncode (List.replicate κ true) (Encoding.Modular.encodeVector width s) := rfl

/-- Encode the Regev ciphertext by concatenating its vector and scalar words
[Pei16, Section 5.2.1, fixed-width representation]. -/
def encodeCiphertext (P : Parameters) (width : ℕ) (c : Ciphertext P) : List Bool :=
  Encoding.Modular.encodeVector width c.1 ++ Candidates.natToList width c.2.val

/-- The ciphertext is the canonical fixed-width vector followed by one MSB-first residue. -/
theorem encodeCiphertext_eq (P : Parameters) (width : ℕ) (c : Ciphertext P) :
    encodeCiphertext P width c =
      Encoding.Modular.encodeVector width c.1 ++ Candidates.natToList width c.2.val := rfl

/-- An exact machine realization of finite Regev bit encryption
[Pei16, Section 5.2.1; PS10, Definition 102.1 and p. 103].
The coin equivalences account for the full uniform tapes. Encryption agrees
with the mathematical map on every canonical public sample, including the
uniform-key hybrid. -/
structure BitRealization (F : LWE.Family) where
  /-- The existing uniform, perfectly correct single-bit scheme. -/
  scheme : BitPublicKeyScheme
  /-- The complete key-generation tape is equivalent to the finite key seed. -/
  keySeed (κ : ℕ) : scheme.gen.Coins κ ≃ KeySeed (F.parameters κ) (F.noise κ)
  /-- The complete encryption tape is equivalent to the independent subset bits. -/
  subset (κ : ℕ) : scheme.enc.Coins κ ≃ (Fin (F.parameters κ).samples → Bool)
  /-- Key generation returns the encoded LWE sample and the corresponding secret. -/
  gen_run (κ : ℕ) (r : scheme.gen.Coins κ) :
    let P := F.parameters κ
    let key := keygen P (F.noise κ) (keySeed κ r)
    scheme.gen.runAt κ [] r = pairEncode
      (LWE.encodeChallenge P (F.residueBits.eval κ) key.1)
      (encodeSecret P (F.residueBits.eval κ) κ key.2)
  /-- Encryption on any canonical public sample runs the finite subset-sum algorithm. -/
  enc_run (κ : ℕ) (pk : PublicSample (F.parameters κ)) (b : Bool) (r : scheme.enc.Coins κ) :
    let P := F.parameters κ
    let w := F.residueBits.eval κ
    scheme.enc.runAt κ (pairEncode (LWE.encodeChallenge P w pk) [b]) r =
      encodeCiphertext P w (encrypt P pk b (subset κ r))
  /-- Decryption on canonical inputs returns the bit from the finite decoder. -/
  dec_run (κ : ℕ) (s : Fin (F.parameters κ).dimension → ZMod (F.parameters κ).modulus)
      (c : Ciphertext (F.parameters κ)) :
    let P := F.parameters κ
    let w := F.residueBits.eval κ
    scheme.dec (pairEncode (encodeSecret P w κ s) (encodeCiphertext P w c)) = [decrypt P s c]

/-- An exact dyadic parameter and noise contract for Regev bit encryption
[Pei16, Definitions 4.2.1 and 4.2.3 and Section 5.2.1, finite-bit specialization].
The bounded integer noise is sampled from a fixed-length fair tape. Its encoded
residue evaluator is the only machine supplied by the profile. The bounds hold
at every parameter, including zero. -/
structure DyadicProfile where
  /-- The exact secret dimension. -/
  dimension : PolyExpr
  /-- The exact number of rows under the common secret. -/
  samples : PolyExpr
  /-- The residue width, with modulus `2^width`. -/
  width : PolyExpr
  /-- The seed length for one noise draw. -/
  noiseBits : PolyExpr
  /-- The integer noise sampled from the full fair-bit seed. -/
  noise (κ : ℕ) : (Fin (noiseBits.eval κ) → Bool) → ℤ
  /-- The evaluator on a pair of the unary parameter and one noise seed. -/
  noiseWord : List Bool → List Bool
  /-- The evaluator is polynomial-time on all inputs. -/
  noiseWord_poly : PolyTimeComputable noiseWord
  /-- The evaluator gives the exact canonical residue of the sampled integer. -/
  noiseWord_run (κ : ℕ) (r : Fin (noiseBits.eval κ) → Bool) :
    noiseWord (pairEncode (List.replicate κ true) (List.ofFn r)) =
      Candidates.natToList (width.eval κ) ((noise κ r : ZMod (2 ^ width.eval κ))).val
  /-- An absolute bound on every noise output. -/
  noiseBound : ℕ → ℕ
  /-- Every parameter uses a modulus of at least two. -/
  width_pos (κ : ℕ) : 0 < width.eval κ
  /-- The integer sampler has the stated bound on every seed. -/
  noise_bounded (κ : ℕ) (r : Fin (noiseBits.eval κ) → Bool) :
    (noise κ r).natAbs ≤ noiseBound κ
  /-- The worst-case subset error satisfies the strict decoding margin. -/
  decoding_margin (κ : ℕ) :
    2 * (samples.eval κ * noiseBound κ) < 2 ^ width.eval κ / 2
  /-- There are enough subset bits for the finite extraction bound at parameter `κ`. -/
  extraction_slack (κ : ℕ) :
    (dimension.eval κ + 1) * width.eval κ + 2 * κ ≤ samples.eval κ

namespace DyadicProfile

/-- At parameter `κ` the dimensions are the two exact polynomial evaluations and
the modulus is the power of two at the prescribed width [Pei16, Definition 4.2.3,
dyadic specialization]. -/
@[simps (config := { isSimp := false }) dimension samples modulus]
def parametersAt (C : DyadicProfile) (κ : ℕ) : Parameters where
  dimension := C.dimension.eval κ
  samples := C.samples.eval κ
  modulus := 2 ^ C.width.eval κ
  modulus_ge_two := by
    have h := C.width_pos κ
    exact Nat.pow_le_pow_right (by decide : 0 < 2) h

/-- The exact dyadic profile gives the existing fixed-sample LWE family with
the specified fair-bit noise law [Pei16, Definition 4.2.3]. -/
@[simps (config := { isSimp := false }) parameters noise dimensionBound samplesBound residueBits]
def family (C : DyadicProfile) : LWE.Family where
  parameters := C.parametersAt
  noise := fun κ => LWE.bitNoise (C.noiseBits.eval κ) (C.noise κ)
  dimensionBound := C.dimension
  samplesBound := C.samples
  residueBits := C.width
  dimension_le := fun _ => Nat.le_refl _
  samples_le := fun _ => Nat.le_refl _
  modulus_le_pow := fun _ => Nat.le_refl _

/-- The key tape has matrix bits, secret bits and independent row-noise blocks. -/
def genCoinBudget (C : DyadicProfile) : PolyExpr :=
  .add (.add (.mul (.mul C.samples C.dimension) C.width) (.mul C.dimension C.width))
    (.mul C.samples C.noiseBits)

/-- The key coin polynomial is the sum of the matrix, secret and row-noise budgets. -/
theorem genCoinBudget_eq (C : DyadicProfile) :
    C.genCoinBudget =
      .add (.add (.mul (.mul C.samples C.dimension) C.width) (.mul C.dimension C.width))
        (.mul C.samples C.noiseBits) := rfl

/-- A uniform key generator with the exact key tape and canonical key outputs implements
the finite key generation [Pei16, Definition 4.2.3 and Section 5.2.1].

**Proof sketch.** Split the tape into full-width matrix and secret blocks and
independent row-noise seeds. Use the bijections in `Encoding.DyadicUniform` and
the finite product regroupings for the complete tape. Compute the matrix-secret
product with `DyadicLinearAlgebra.matVecPoly`. Use the registered H16 counted word
loop to consume the product words and noise seeds row by row, applying
`noiseWord` and `DyadicArithmetic.addPoly`. Retain the original matrix for the
public word and the original secret for the secret word. Each accumulated
residue is width-bounded, and the unconsumed input and retained context are
bounded by the raw input length. The run equation follows from the codec
readers and `keygen_fst` and `keygen_snd`. -/
theorem exists_keygenMachine (C : DyadicProfile) :
    ∃ G : NUPPT, G.Uniform ∧ G.coins = C.genCoinBudget ∧
      ∃ seed : ∀ κ, G.Coins κ ≃ KeySeed (C.family.parameters κ) (C.family.noise κ),
        ∀ κ (r : G.Coins κ),
          let P := C.family.parameters κ
          let key := keygen P (C.family.noise κ) (seed κ r)
          G.runAt κ [] r = pairEncode (LWE.encodeChallenge P (C.width.eval κ) key.1)
            (encodeSecret P (C.width.eval κ) κ key.2) := by
  sorry

/-- A uniform encryptor with one fair bit per row implements the exact encoded
subset-sum encryption on every canonical public key [Pei16, Section 5.2.1].

**Proof sketch.** Walk the matrix, value vector and subset tape together for the
exact row count using H16. For a selected row, use an inner H16 loop with
`DyadicArithmetic.addPoly` to add its entries and value into a fixed-width
accumulator. Each inner word is padded or truncated to the scheduled width
even on malformed inputs. The state contains only the bounded context,
unconsumed input and the scheduled accumulator. Add the bit codepoint to
the final scalar. The row invariant is the sum of exactly the selected
rows so far, which gives both projections of `encrypt`. -/
theorem exists_encryptMachine (C : DyadicProfile) :
    ∃ E : NUPPT, E.Uniform ∧ E.coins = C.samples ∧
      ∃ subset : ∀ κ, E.Coins κ ≃ (Fin (C.family.parameters κ).samples → Bool),
        (∀ κ (r : E.Coins κ), List.ofFn (subset κ r) = List.ofFn r) ∧
        ∀ κ (pk : PublicSample (C.family.parameters κ)) (b : Bool) (r : E.Coins κ),
          let P := C.family.parameters κ
          let w := C.width.eval κ
          E.runAt κ (pairEncode (LWE.encodeChallenge P w pk) [b]) r =
            encodeCiphertext P w (encrypt P pk b (subset κ r)) := by
  sorry

/-- A deterministic polynomial-time decryptor on encoded secrets and ciphertexts
agrees with the finite nearest-codepoint decoder [Pei16, Section 5.2.1;
Wu24, Definition 20.5].

**Proof sketch.** Read the parameter from the secret word. Cut the ciphertext
at the scheduled vector length, evaluate the inner product with
`DyadicLinearAlgebra.dotPoly`, then apply `DyadicArithmetic.subPoly`.
At width one, the residual itself is the bit. At larger widths, the true
codepoint is nearer precisely on the open interval from a quarter to
three quarters of the modulus. Compare the fixed-width residual to these
two endpoints. The strict comparisons give the false tie convention. -/
theorem exists_decryptor (C : DyadicProfile) :
    ∃ dec : List Bool → List Bool, PolyTimeComputable dec ∧
      ∀ κ (s : Fin (C.family.parameters κ).dimension → ZMod (C.family.parameters κ).modulus)
        (c : Ciphertext (C.family.parameters κ)),
        let P := C.family.parameters κ
        let w := C.width.eval κ
        dec (pairEncode (encodeSecret P w κ s) (encodeCiphertext P w c)) = [decrypt P s c] := by
  sorry

/-- A dyadic profile gives a perfectly correct realization in the existing bit PKE
interface [Pei16, Section 5.2.1; PS10, Definition 102.1 and p. 103].

**Proof sketch.** Assemble the three machines using their equations and
uniformity proofs. Read the bounded integer sampler through `bitNoise_sample`
and apply `decrypt_keygen_encrypt` with the profile's strict margin at each
parameter. The same machine equations supply the realization fields. -/
theorem exists_bitRealization (C : DyadicProfile) : Nonempty (BitRealization C.family) := by
  sorry

end DyadicProfile

end TCSlib.Cryptography.Encryption.PublicKey.Regev
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/Regev/Security.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Implementation
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev single-bit ensemble security

## Main results

The finite Regev advantage bound transfers to the existing single-bit game
with two fixed non-uniform PPT reductions. The exact sample schedule of the
dyadic profile makes the extraction term negligible. The existing bitwise
and fixed-batch lifts apply to the resulting scheme.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3 and Section 5.2.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Definition 102.2 and p. 103.
-/

namespace TCSlib.Cryptography.Encryption.PublicKey.Regev

open Complexity

namespace BitRealization

/-- The machine's false-versus-true advantage is bounded by two fixed-sample
DLWE advantages and the finite extraction error
[Pei16, Section 5.2.1; PS10, Definition 102.2 and p. 103].
The two reduction machines are fixed for the entire security-parameter family.

**Proof sketch.** For each bit, precompose the scheme's encryptor with pairing
the challenge word with that bit. Use `NUPPT.exists_seq` to pass the challenge
word and the resulting ciphertext to the distinguisher on a fresh tape.
The first tape, transported by the realization's subset equivalence, and
the unchanged distinguisher tape form the coin type of the finite reduction.
Use the key-generation and encryption equations and `pkEncDist_eq` to read
the real scheme view as the encoded finite view. Transport uniform seeds
by the two coin equivalences. For each machine, read `Family.advantageAt_eq`
and use the sequential composition equation on every encoded challenge key.
These probability identities turn `distAdv_encrypt_le` into the claimed bound. -/
theorem advantage_le {F : LWE.Family} (I : BitRealization F) (D : NUPPT) :
    ∃ R₀ R₁ : NUPPT, ∀ κ,
      distAdv (I.scheme.pkEncDist κ false) (I.scheme.pkEncDist κ true)
        (D.distinguisherL κ) ≤
        F.advantageAt R₀ κ + F.advantageAt R₁ κ + 2 * extractionError (F.parameters κ) := by
  sorry

/-- The existing bit PKE ensemble is secure under the family's fixed-sample DLWE
assumption and the extraction slack [Pei16, Section 5.2.1; PS10, p. 103].

**Proof sketch.** Specialize the quantitative bound to a distinguisher.
Both fixed reduction advantages are negligible by `dlweAssumption_iff`.
The representation bound and the sample slack give an extraction bound
of `2^(-κ)` by `two_extractionError_le`. Dominate the nonnegative game
advantage by the sum of the three negligible terms and apply
`BitPublicKeyScheme.singleBitSecure_iff`. -/
theorem singleBitSecure_of_DLWE {F : LWE.Family} (I : BitRealization F)
    (hslack : ∀ κ, ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤
      (F.parameters κ).samples)
    (hLWE : LWE.DLWEAssumption F) : I.scheme.SingleBitSecure := by
  sorry

end BitRealization

namespace DyadicProfile

/-- The dyadic Regev construction gives a correct bit scheme with single-bit
security and its bitwise extension has fixed-message and fixed-batch security
[Pei16, Section 5.2.1; PS10, Definition 102.2 and p. 103].
The batch uses one public key and independent encryption coins.

**Proof sketch.** Obtain the exact machine realization. Read the profile's
polynomial dimension, width and sample count and apply its extraction slack
to the bit security theorem. Use the owner's `SingleBitSecure.bitwise` and
`Secure.multiMessageSecure` theorems for the two fixed-message endpoints. -/
theorem exists_secureBitScheme (C : DyadicProfile) (hLWE : LWE.DLWEAssumption C.family) :
    ∃ I : BitRealization C.family,
      I.scheme.SingleBitSecure ∧ I.scheme.bitwise.Secure ∧ I.scheme.bitwise.MultiMessageSecure := by
  sorry

end DyadicProfile

end TCSlib.Cryptography.Encryption.PublicKey.Regev
```


## ===== briefs/lwe-sis-constructions/continuation/regev-bit-security/REPORT.md =====

```text
# Regev bit-encryption statement phase

| Pin | Revision |
|---|---|
| Verified merge of PR #280 | `f967299b6a0bde5b7efa4062b2b55046ebd21387` |
| Verified merge tree | `1bdbc5b7e6c3d5a47778df8de7e8c479ce934f49` |
| Proposed source | `fe34bcf656be930f3ea39a10df74110695c95ed4` |

The merge tree matches the integration tree checked for PR #280. The source
commit adds two Regev-owned modules. The separate export patch supplies the
two facade imports and updates the facade's scope description. Its prospective
bytes were used for the sweep.

## Statement surface

- `Implementation.lean` specifies the canonical wires, exact dyadic
  schedules, supplied bounded noise-word evaluator, independent tapes, and
  machine realization in `BitPublicKeyScheme`.
- `Security.lean` states the two-machine quantitative bound, the
  fixed-sample DLWE lift, and the existing fixed-message and fixed-batch endpoints.
- The arithmetic proofs in the profile constructor and the definitional reader
  equations are included in the audit. The seven remaining bodies are statement
  admissions.

## Verification

- The fresh prospective root closure contains **1,171 modules**.
  Lean 4.25.0 reported zero errors using the pinned Lake packages.
- Four expected admissions occur in the implementation module and three in the
  security module. The 231 inherited warnings
  have the same per-module counts as the verified parent.
- The scoped style lint returned zero failures and zero warnings. The
  `import TCSlib` probe resolved the seven statements and checked their
  axiom inventories.
- The checked wire and profile definitions use only standard axioms. The seven
  statement stubs depend on `sorryAx` as intended.

[Verification](VERIFICATION.json)
[Proposed export](proposed-regev-export.patch)
[Root probe](RegevRootProbe.lean) · [Probe log](regev-root-probe.log)

The next gate is independent statement review. Proof fill follows the accepted
statements. Adaptive IND-CPA uses the separate oracle-game owner.
```


## ===== briefs/lwe-sis-constructions/continuation/regev-bit-security/VERIFICATION.json =====

```text
{
  "base": "f967299b6a0bde5b7efa4062b2b55046ebd21387",
  "base_tree": "1bdbc5b7e6c3d5a47778df8de7e8c479ce934f49",
  "toolchain": "leanprover/lean4:v4.25.0",
  "whole_library_root_modules": 1171,
  "whole_library_errors": 0,
  "whole_library_fresh_project_objects": true,
  "unchanged_parent_modules_with_identical_admission_counts": 1168,
  "new_source_declarations": 23,
  "intentional_statement_admissions": {
    "TCSlib/Cryptography/Encryption/PublicKey/Regev/Implementation": 4,
    "TCSlib/Cryptography/Encryption/PublicKey/Regev/Security": 3
  },
  "inherited_admission_warnings": 231,
  "proposed_facade_patch_sha256": "6cd8fd8e3cefb6e785fdec5cc2de9a0c34ebfce476fd889f33a4532a4a90694b",
  "prospective_facade_sha256": "91466fc070e2ca8bbb8b411a5638f88e1b7419e9b1cbca2db8a0663d2e86a1fa",
  "new_sources_sha256": {
    "TCSlib/Cryptography/Encryption/PublicKey/Regev/Implementation.lean": "62e1a00d2fc743472f44d53cda0198f493d68a05cfd739071ab1e4ee8fd0e124",
    "TCSlib/Cryptography/Encryption/PublicKey/Regev/Security.lean": "0d1cdfda6366221935e0d2eeb7cb3d4638828f597becddc81d6180ab7b0943b2"
  },
  "axioms": {
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_keygenMachine": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_encryptMachine": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_decryptor": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_bitRealization": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.BitRealization.advantage_le": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.BitRealization.singleBitSecure_of_DLWE": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_secureBitScheme": [
      "Classical.choice",
      "Quot.sound",
      "propext",
      "sorryAx"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.encodeSecret": [
      "propext"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.encodeCiphertext": [
      "propext"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.parametersAt": [
      "Classical.choice",
      "Quot.sound",
      "propext"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.family": [
      "Classical.choice",
      "Quot.sound",
      "propext"
    ],
    "TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.genCoinBudget": [
      "Classical.choice",
      "Quot.sound",
      "propext"
    ]
  },
  "root_probe_log_sha256": "654f0988b2c900d1c014debe1398095a734bd9dd5bb7db37dd90687aa3ed428c",
  "module_receipts_sha256": "1ea7a9718b4c7d324018467a4431a53db1541449ed7c4e22a976ab140ff5e110",
  "whole_library_log_archive_sha256": "da7c37c5874083a65704ca8ef937fb90c4778beb19427669b04d74975404d398",
  "source": "fe34bcf656be930f3ea39a10df74110695c95ed4"
}
```


## ===== briefs/lwe-sis-constructions/continuation/regev-bit-security/proposed-regev-export.patch =====

```text
--- a/TCSlib/Cryptography/Encryption/PublicKey/Regev.lean
+++ b/TCSlib/Cryptography/Encryption/PublicKey/Regev.lean
@@ -4,6 +4,8 @@
 -/
 import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
 import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments
+import TCSlib.Cryptography.Encryption.PublicKey.Regev.Implementation
+import TCSlib.Cryptography.Encryption.PublicKey.Regev.Security

 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -16,9 +18,9 @@

 * `Basic`: mathematical keygen/encryption/decryption and strict bounded-error correctness.
 * `Experiments`: explicit DLWE hybrids, binary extraction and quantitative security bounds.
+* `Implementation` specifies the dyadic profile, uniform machines and exact wire equations.
+* `Security` specifies the fixed-sample DLWE reduction and ensemble security endpoints.

-All nontrivial new statements are admitted for the combined statement audit.
-The child modules distinguish actual laws and deterministic mathematics from
-efficiency/security endpoints. Source-policy work and user-controlled integration
-remain open; this facade claims no completed primitive or CCA2 security.
+The finite correctness and advantage bound are proved. The machine and
+ensemble security statements are prepared for the statement audit.
 -/
```


## ===== briefs/lwe-sis-constructions/continuation/regev-bit-security/RegevRootProbe.lean =====

```text
import TCSlib

open TCSlib.Cryptography.Encryption.PublicKey.Regev

#check DyadicProfile.exists_keygenMachine
#print axioms DyadicProfile.exists_keygenMachine
#check DyadicProfile.exists_encryptMachine
#print axioms DyadicProfile.exists_encryptMachine
#check DyadicProfile.exists_decryptor
#print axioms DyadicProfile.exists_decryptor
#check DyadicProfile.exists_bitRealization
#print axioms DyadicProfile.exists_bitRealization
#check BitRealization.advantage_le
#print axioms BitRealization.advantage_le
#check BitRealization.singleBitSecure_of_DLWE
#print axioms BitRealization.singleBitSecure_of_DLWE
#check DyadicProfile.exists_secureBitScheme
#print axioms DyadicProfile.exists_secureBitScheme
#print axioms encodeSecret
#print axioms encodeCiphertext
#print axioms DyadicProfile.parametersAt
#print axioms DyadicProfile.family
#print axioms DyadicProfile.genCoinBudget
```


## ===== briefs/lwe-sis-constructions/continuation/regev-bit-security/regev-root-probe.log =====

```text
TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_keygenMachine (C : DyadicProfile) :
  ∃ G,
    G.Uniform ∧
      G.coins = C.genCoinBudget ∧
        ∃ seed,
          ∀ (κ : ℕ) (r : G.Coins κ),
            let P := C.family.parameters κ;
            have key := keygen P (C.family.noise κ) ((seed κ) r);
            G.runAt κ [] r =
              Turing.pairEncode (TCSlib.Cryptography.LWE.encodeChallenge P (C.width.eval κ) key.1)
                (encodeSecret P (C.width.eval κ) κ key.2)
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_keygenMachine' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_encryptMachine (C : DyadicProfile) :
  ∃ E,
    E.Uniform ∧
      E.coins = C.samples ∧
        ∃ subset,
          (∀ (κ : ℕ) (r : E.Coins κ), List.ofFn ((subset κ) r) = List.ofFn r) ∧
            ∀ (κ : ℕ) (pk : PublicSample (C.family.parameters κ)) (b : Bool) (r : E.Coins κ),
              let P := C.family.parameters κ;
              have w := C.width.eval κ;
              E.runAt κ (Turing.pairEncode (TCSlib.Cryptography.LWE.encodeChallenge P w pk) [b]) r =
                encodeCiphertext P w (encrypt P pk b ((subset κ) r))
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_encryptMachine' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_decryptor (C : DyadicProfile) :
  ∃ dec,
    Complexity.PolyTimeComputable dec ∧
      ∀ (κ : ℕ) (s : Fin (C.family.parameters κ).dimension → ZMod (C.family.parameters κ).modulus)
        (c : Ciphertext (C.family.parameters κ)),
        let P := C.family.parameters κ;
        have w := C.width.eval κ;
        dec (Turing.pairEncode (encodeSecret P w κ s) (encodeCiphertext P w c)) = [decrypt P s c]
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_decryptor' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_bitRealization (C : DyadicProfile) :
  Nonempty (BitRealization C.family)
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_bitRealization' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
TCSlib.Cryptography.Encryption.PublicKey.Regev.BitRealization.advantage_le {F : TCSlib.Cryptography.LWE.Family}
  (I : BitRealization F) (D : Complexity.NUPPT) :
  ∃ R₀ R₁,
    ∀ (κ : ℕ),
      TCSlib.Cryptography.distAdv (I.scheme.pkEncDist κ false) (I.scheme.pkEncDist κ true) (D.distinguisherL κ) ≤
        F.advantageAt R₀ κ + F.advantageAt R₁ κ + 2 * extractionError (F.parameters κ)
'TCSlib.Cryptography.Encryption.PublicKey.Regev.BitRealization.advantage_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
TCSlib.Cryptography.Encryption.PublicKey.Regev.BitRealization.singleBitSecure_of_DLWE
  {F : TCSlib.Cryptography.LWE.Family} (I : BitRealization F)
  (hslack : ∀ (κ : ℕ), ((F.parameters κ).dimension + 1) * F.residueBits.eval κ + 2 * κ ≤ (F.parameters κ).samples)
  (hLWE : TCSlib.Cryptography.LWE.DLWEAssumption F) : I.scheme.SingleBitSecure
'TCSlib.Cryptography.Encryption.PublicKey.Regev.BitRealization.singleBitSecure_of_DLWE' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_secureBitScheme (C : DyadicProfile)
  (hLWE : TCSlib.Cryptography.LWE.DLWEAssumption C.family) :
  ∃ I, I.scheme.SingleBitSecure ∧ I.scheme.bitwise.Secure ∧ I.scheme.bitwise.MultiMessageSecure
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.exists_secureBitScheme' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Encryption.PublicKey.Regev.encodeSecret' depends on axioms: [propext]
'TCSlib.Cryptography.Encryption.PublicKey.Regev.encodeCiphertext' depends on axioms: [propext]
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.parametersAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.family' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Encryption.PublicKey.Regev.DyadicProfile.genCoinBudget' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```


## ===== workflow.md =====

````text
# TCSlib Formalization Workflow

How large formalization campaigns are run in this repository. [`policy.md`](policy.md)
says what landed Lean code must look like; this document says what *process* produces
it. The reference implementation is the Arora-Barak campaign
(`AroraBarakChapter1Plan.md`, complete and audited end to end;
`AroraBarakChapter2Plan.md`, in progress) — file paths below cite its artifacts as
worked examples. Where an older document describes a mechanism this one supersedes
(e.g. the PR-based fill delivery in `AroraBarakChapter1Plan.md` §5, since replaced by
zip delivery), this document records current practice.

```
plan  →  statement phases  →  audit gates  →  fill campaign  →  closure
          (sorry-skeletons)    (per phase)     (epochs/batches)   (attestation, final
                                                                   audit, blueprint)
```

The load-bearing idea: **statements are audited before proofs are attempted.** Lean
already checks proofs; the dominant failure mode of formalization is a wrong or
subtly-weakened *statement*, and that is cheapest to catch while everything is still a
`sorry`. Every phase therefore lands as a compiling skeleton, passes an adversarial
external audit gate, and only then becomes fill work.

## 1. The campaign plan

Each campaign (typically one textbook chapter) begins with a plan file at the repo
root — `<Source>Chapter<N>Plan.md` — containing:

* **Scope**: which results are mandatory core, which are deferred, with source
  citations.
* **Foundation decisions**: the definitional conventions, each with its rationale
  (these are where audits bite; see §3).
* **Architecture and module layout**: directories, namespaces, facades, per policy §1.
* **Phasing**: the statement phases and the anticipated fill epochs.
* **Risks and honest effort assessment**.
* **Open design questions (human review required)**: decisions reserved for a human
  maintainer. Audit rounds *verify* these but never *dispose* of them; each records
  the maintainer's provisional choice and stays open until a human closes it. The
  consolidated register — full statements, cross-links, and status — is
  [`backlog.md`](backlog.md); the plans keep stable numbered stubs, which is what
  audit documents cite.
* **Decision log**: an append-only table. Every methodological decision, every audit
  round's verdict, and every repair round gets a row. The log is the campaign's
  memory; when a decision is reversed, the old row is marked **Superseded** in place,
  never deleted.

## 2. Statement phases (sorry-skeletons)

A phase lands the definitions plus the theorem *statements* of one coherent slice,
every proof a `sorry` under a policy-grade proof sketch (policy §3: the sketch is
written at skeleton time and is the plan; a skeleton whose sketch cannot be written is
not ready to land). Ground rules:

* Definitions and sorried statements only. Proofs appear in a skeleton only for
  definitional-unfolding lemmas whose home module mirrors proved infrastructure (the
  precedent: the `runWith` algebra of `TuringMachine/Nondeterministic.lean`, mirroring
  the vendored `runFrom` lemmas), and any such deviation is flagged in the audit pack
  with the proofs declared part of the audited surface.
* Sketches name their obligations: a sketch that will need a machine construction
  names each sub-machine as an explicit fill obligation, so the eventual brief can
  inherit the list. It also names every **host** the route needs (policy §1, **Hosts come
  first**), from the registry in `machine-library-design.md` §14. A sketch that needs an
  unregistered host is not ready: the host's public contract is a statement-phase item of
  its own, gated before the consumer's fill.
* Everything gate-verifies before commit: per-module checks plus a full fresh sweep
  (§6), style lint, and the headline axiom prints.

## 3. Audit gates (between phases)

Right after a skeleton lands — statements frozen — an **external adversarial audit**
runs before any fill or any next phase. The auditor is an LLM from a different vendor,
in a fresh context, reviewing the trusted surface (definitions, statements, sketches,
and any skeleton-time proofs) against the source text.

**Artifacts**, committed under `audits/` with campaign-scoped names
(`ch2-phase1-*`, `epoch4-*`), except the bundle:

* `…-pack.md` — the auditor's instructions: the audited commit, repository-side
  attestations (freeze by path enumeration, sweep results, admission inventory, axiom
  prints, lint — stated so the auditor can verify or challenge them, with source facts
  kept separate from maintainer execution claims), the under-audit inventory, a
  prioritized brief (the plan's seeded design questions go here), and the findings
  table format with the severity guide: **blocker** (a downstream phase would build on
  a wrong statement) / **major** (fixable but materially misleading) / **minor** /
  **note**. `campaign/standards/TEMPLATE.md` is the skeleton.
* `…-bundle.md` — a single uploadable file: the pack verbatim, then every attachment
  under a `## ===== <path> =====` header (prior findings, both plans, `policy.md`,
  the root, and the full module tree). **Not committed** (user, 2026-10-15): it is kept
  in the local dispatch folder, and the resolutions record its SHA-256 and section
  count. Bundles committed before then are indexed in `campaign/BUNDLES.md`, with how to
  retrieve them from history.
* A short kickoff message (drafted per round, pasted by the maintainer into a fresh
  auditor chat with the bundle attached).
* `…-findings.md` — the auditor's report, preserved **verbatim**, including anything
  the maintainer disputes. Pack errata found later are acknowledged in the resolutions
  file; shipped packs are never edited retroactively.

**The gate rule**: a gate closes only on a round reporting **zero blockers and zero
majors**. A round with majors triggers repairs and a full re-audit round (minors may
be swept in the closing commit and re-verified). Repairs adopt the auditor's own
constructions where supplied, are re-gated, and are recorded in the decision log; when
the loop closes, `…-resolutions.md` summarizes every round, every repair, and the note
dispositions. The complete worked example is the three-round
`campaign/gates/ch2-phase1{,-reaudit,-round3}/{pack,findings,resolutions}.md` loop.

Audits complement, never replace, in-Lean sanity theorems — the machine-checked and
permanent form of the same checks.

## 4. The fill campaign (epochs and batches)

With all phase gates closed, the audited-true sorries are filled in **epochs** —
sequential, ordered by risk retirement, with an audit round at each epoch boundary —
each consisting of **batches** run in parallel by cloud agents with disjoint file
ownership, from self-contained briefs in `briefs/`.

**Binding batch ground rules** (full text repeated in every brief):

1. **Exclusive file ownership.** Helpers live `private` in owned files; a lemma that
   belongs in a shared file is *requested* in the report and added serially at epoch
   merge, flagged for the next audit. **Hosts are the exception** (rule 4).
2. **Statement freeze.** Audited declarations are never renamed, re-signatured, or
   re-stated by fill work. A target that looks unprovable as stated is an
   *escalation*, reported with the obstruction — never "fixed" inline.
3. **Verification per batch**: the check script (§6) over the owned files, zero
   `error:` lines, sorries only at documented out-of-scope items.
4. **Hosts first** (user, 2026-10-12; policy §1). A batch never builds a search,
   recursion, interpreter, runner or input device as a private one-off. It cites the
   registered public host its brief names. If the route turns out to need a host the
   brief does not name, that is an escalation, reported with the contract the batch
   would need; the batch continues on its other targets.

**Hosts in briefs.** A fill brief is issued only when every host its route needs is
registered (`machine-library-design.md` §14) and the host's statement gate has closed. The
host's own fill may run in the same wave, in its own batch, with consumers citing it under
the proved-modulo rule. The readiness check for any target lists the hosts it needs. A
private host already in the tree is harvested (a promotion PR and its gate) before a second
consumer is briefed against it.

**Delivery is by zip, not PR.** Each batch returns an archive containing `REPORT.md`,
the full source files, a `git format-patch` series, a git bundle, the batch's sweep
log, the axiom-print log, and `SHA256SUMS`. The maintainer verifies before
integrating: checksums; the statement freeze (comment-stripped comparison of every
audited signature); enumeration of any removals; public-declaration drift; a full
fresh sweep; the headline axiom prints; and the **duplication ledger** — every
private copy of existing proved material in the delivery enumerated, with each
touched file's cumulative copied-material count and fraction. If a delivery pushes a
file past **one fifth copied material**, or adds copies to a file that already
received copies in an earlier epoch, the maintainer opens a `backlog.md` §1
human-review item before the epoch's audit pack ships — no discretion. Integration
is `git am -3` from the patch series, preserving the agent's authorship. Large fills that exhaust one agent's budget
continue via a continuation brief to a fresh agent (the `universal` B2 precedent).

**Counting public names** (user, 2026-10-22; gate 59). Public-declaration drift, the statement
freeze and a brief's "no new public declaration" rule count **public declarations**: the
declarations the source introduces without `private` (`theorem`, `lemma`, `def`, `abbrev`,
`instance`, `structure`, `inductive`, `class`), counted by the comment-aware source census
(`devtools/seyoon/declfreeze.py`). Packs say so ("N → N public declarations, at source"). A
**public constant** is a non-private name in the module's elaborated environment (the axiom
probe's walk of the module's publics). Packs and reviews report a module's new public constants
separately, by kind:
- a declaration's compiler auxiliaries (`_proof_N`, `_simp_N`, `match_N`, `eq_N`, `eq_def`,
  `congr_simp`);
- the instances that `deriving` generates for a **private** type, which Lean 4.25 names publicly
  (e.g. `instDecidableEqSl_Key`).

Neither kind is a public declaration. A derived instance of a private type needs no finding when
its type is private to its file and a name check over the tree and the open PRs finds no clash;
where a derived name would clash, write an explicit `private instance`. Any other new public
constant is reported as a finding.

**Epoch boundaries**: the maintainer re-runs the full sweep, produces a **drift
attestation** (§6), and prepares the epoch's audit pack with elaboration evidence
and the epoch's **duplication ledger**, which the auditor verifies independently
(audit template failure mode 5); the epoch's gate follows the same
zero-blockers/majors rule as phase gates, and a debt major closes only by explicit
human acknowledgment recorded in the resolutions file. Once a family is
acknowledged, later corrections to its accounting are minors (audit template
failure mode 5) and do not hold the gate; the ledger is still corrected.

## 5. Closure

When the last sorry falls: a zero-sorry sweep with build evidence; a campaign-wide
drift attestation against the audited baselines; a final audit pack covering the fill
rounds; and the blueprint increment — dependency graph from `.ilean` artifacts,
`scripts/blueprint_{enumerate,assemble,validate}.py`, blueprint-writer agents, with
the blueprint **late-bound** throughout (extraction only at boundaries; no blueprint
LaTeX hand-written ahead of the Lean; `blueprint/BLUEPRINT_PIPELINE.md` has the
pipeline detail).

## 6. Verification tooling

* **`scripts/lean_check_tree.sh <module>`** — the campaign's elaboration gate: a
  direct `lean` invocation per module (**`lake build` is banned on campaign
  branches** — see the Chapter-1 decision log), emitting fresh `.olean`s into a
  scratch tree. Pass requires exit 0, zero `error:` lines, *and* a fresh olean, so a
  stale artifact can never satisfy the check. The full sweep runs it over every
  module, in dependency order, from `scripts/ab_ch1_module_order.txt`:

  ```
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < scripts/ab_ch1_module_order.txt )
  ```

  Admission counting is by `declaration uses 'sorry'` warnings in the sweep log; the
  expected count is attested in every pack.
* **`scripts/campaign_style_lint.py`** (named `scripts/style_lint.py` until the
  main merge, which adopted main's per-file policy linter under that name — the
  historical audit logs' invocations refer to this tool) — mechanical policy checks: statement-prose docstrings,
  sketch-before-sorry, file sizes, `## References`, facade coverage, and (check 8, since
  2026-10-16) public definitions without a lemma beside them (`policy.md` §1, *Definitions
  land with their lemmas*). Campaign baseline: zero FAIL (legacy pre-campaign files outside
  the audited surface are tolerated and listed). Check 8 is a WARN listing names; a landing
  adds no name to it.
* **Axiom prints** — `#print axioms` for every headline theorem on the *fresh* olean
  tree: closed results must show exactly `[propext, Classical.choice, Quot.sound]`;
  sorried statements show `sorryAx`, and any other axiom is a stop-the-line event.
* **Drift attestation** — the anti-tamper check between audited baselines: strip
  comments from every module, compare both the **multiset** of declarations and the
  **ordered declaration sequence** against the baseline, and enumerate public
  declarations (gained / lost / changed) so that "nothing audited moved" is a checked
  claim, not an impression.
* **Vendored files** are frozen at their recorded upstream pin and periodically
  byte-compared against upstream; local modifications live only in the header list.

## 7. Relationship to the other documents

* [`ROADMAP.md`](ROADMAP.md) — a one-page orientation: the phases ahead and pointers to
  the documents that hold the detail.
* [`policy.md`](policy.md) — the standards this workflow enforces (modularity,
  attribution, sketches, review checklist).
* [`lean-glossary.md`](lean-glossary.md) — the Lean/Mathlib jargon appearing in
  declaration names and docstrings (fuel, Sigma, `Prop` vs `Bool`, the naming
  grammar, …), for readers fluent in TCS but not in Lean.
* [`AGENTS.md`](AGENTS.md) / `.claude/` — the sorry-ladder proof technique and agent
  roster; useful *inside* a fill batch, but campaign verification runs through §6, not
  through `lake build` or editor-only checks.
* [`blueprint/BLUEPRINT_PIPELINE.md`](blueprint/BLUEPRINT_PIPELINE.md) — blueprint
  generation and validation.
* [`.github/copilot-instructions.md`](.github/copilot-instructions.md) — main-branch
  build and CI; campaign branches deviate as recorded in their decision logs.
````


## ===== policy.md =====

````text
# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
````


## ===== AGENTS.md =====

````text
# Lean 4 Proof Assistant System

This directory contains a coordinated multi-agent system for writing Lean 4 proofs incrementally, using **sorry-driven development** to avoid token-limit failures.

**All Lean contributions must follow the repository standards in [`policy.md`](policy.md)** — modularity (file layout, size, namespaces, exports), attribution (every result traced to a textbook/paper reference via docstring tags and blueprint sources), and human-readable proof sketches accompanying every nontrivial proof. Read it before writing or landing any Lean code.

## Core Principle: The Sorry Ladder

Lean's `sorry` tactic closes any goal and makes the file compile. This means you can:

1. Write the theorem statement and check it typechecks (with `sorry` as the body)
2. Sketch the full `have`/`calc`/`obtain` structure — all sub-goals `sorry`'d out
3. Fill in one `have` block at a time, checking after each
4. Never write more than one tactic block per agent invocation

This is the only reliable way to write long Lean proofs without hitting the token limit or producing uncheckable code.

## Directory Layout (created at runtime)

```
lean_proof/
  OUTLINE.md          ← Proof plan: theorem, strategy, step list with sorry-stubs
  Main.lean           ← The live Lean file (always compilable — sorry fills gaps)
  search_log.md       ← Mathlib lemma search results (for reuse across steps)
  error_log.md        ← Error history with resolutions (learn from past errors)
  step_NN.md          ← Scratch notes for individual steps (optional)
```

## Available Agents

| Agent | Purpose |
|---|---|
| `lean-orchestrator` | Plans proof structure, writes sorry-skeleton, manages OUTLINE.md |
| `lean-prover` | Fills in one sorry-stub in Main.lean with real tactics |
| `lean-searcher` | Finds Mathlib lemmas using exact?, apply?, simp?, and name search |
| `lean-checker` | Reads Main.lean for sorry status; error info comes from VS Code LeanInfoView (no build commands) |
| `lean-formatter` | Converts papers/PDFs into Lean-friendly markdown (definitions, theorem statements) |

## Available Commands

| Command | Usage |
|---|---|
| `/lean-prove` | Start a new Lean proof — provide the theorem statement |
| `/lean-step` | Fill in a specific sorry-stub by number |
| `/lean-search` | Search Mathlib for lemmas matching a description |
| `/lean-check` | Run Lean on Main.lean and interpret any errors |
| `/lean-status` | Show which sorry-stubs remain and overall progress |

## Workflow

```
# 1. Start
/lean-prove "theorem foo (n : ℕ) : n + 0 = n"

# 2. Inspect the sorry-skeleton in lean_proof/Main.lean
# 3. Fill in steps one at a time
/lean-step 1      # writes real tactics for sorry #1
/lean-check       # verify it compiles
/lean-step 2
/lean-check
...

# 4. Search Mathlib when stuck
/lean-search "commutativity of addition natural numbers"

# 5. Done when lean-check shows 0 errors and 0 sorrys
```

## Debugging and Error Inspection

**Always use the VS Code LeanInfoView to get goal state and error information — never run `lake build`, `lean`, or any other build command.**

The LeanInfoView (the Lean infoview panel in VS Code) shows:
- The current tactic goal state at the cursor position
- Any type errors or tactic failures inline
- `exact?` / `apply?` / `simp?` suggestions in real time

To inspect a goal or error:
1. Place the cursor inside the tactic block in VS Code
2. Read the goal state from the LeanInfoView panel
3. Use that information to decide the next tactic

Do not invoke shell commands (`lake build`, `lean --check`, etc.) to check proof state. The LeanInfoView is the authoritative, zero-latency source of truth.

## Lean 4 Tactic Cheatsheet (for agent reference)

| Tactic | Use |
|---|---|
| `sorry` | Placeholder — closes any goal |
| `exact h` | Close goal with term `h` |
| `apply lemma` | Reduce goal using `lemma` |
| `rw [lemma]` | Rewrite using equation |
| `simp [lemmas]` | Simplification |
| `ring` | Ring identity |
| `linarith` | Linear arithmetic over ordered field |
| `omega` | Linear arithmetic over ℕ/ℤ |
| `norm_num` | Numerical computation |
| `decide` | Decidable propositions |
| `aesop` | General purpose automation |
| `have h : T := by ...` | Introduce intermediate fact |
| `obtain ⟨a, ha⟩ := h` | Destructure existential |
| `rcases h with ...` | Pattern match hypothesis |
| `induction n with` | Induction |
| `by_contra h` | Proof by contradiction |
| `push_neg` | Push negations inward |
| `contrapose` | Switch to contrapositive |
| `calc` | Chain of equalities/inequalities |
| `exact?` | Ask Lean to find a proof term |
| `apply?` | Ask Lean to find applicable lemma |
| `simp?` | Ask Lean which simp lemmas apply |
````


## ===== machine-library-design.md =====

````text
# Machine-construction library — design document

Status: **FROZEN 2026-10-03** — the open decisions in §9 were resolved by the
user (resolutions recorded inline there). No code exists yet; every Lean
snippet below is an interface *shape*, not a final signature — final
signatures are fixed at spec time and audited.

Evidence base: the epoch-2 checkpoint integration (decision-log row,
2026-10-03). All five open fill frontiers are concrete-machine construction;
147 private helpers were delivered in one epoch, dominated by re-built
copiers, scanners, counters, capture wrappers, and phase glue. The
capture/silence wrapper alone now has four private incarnations
(`universalCaptureTM`, `enumCaptureTM`, `acceptTM`, and the private engine
inside `Composition.lean`'s `exists_cond`).

Prior-art disposition (2026-10-03 discussion): Mathlib's TM2 framework is a
stack-machine model whose poly-time layer contains one machine (the identity)
and no composition theorem; its inter-model compilations are semantics-only.
Decision: build on our own `FinTM` multi-tape model, which owns all the
quantitative assets; adopt the *design idiom* of Mathlib's TM1 statement
language (labelled structured control) for how named machines are written,
import nothing.

## 1. Goals and non-goals

**Goal.** Make "build a finite machine with a proved polynomial time bound"
a library-call activity rather than a bespoke construction, at the
granularity the fill briefs actually need: parse, measure, evaluate a
polynomial, search, split, compare, copy, emit, run a subroutine silently,
branch, loop.

**Non-goals.**
- ~~No deep-embedded language, no verified compiler, no cost-sound surface
  syntax. (Mature end state; not justified by the remaining campaign.)~~
  **Superseded (user, 2026-10-12): a programming layer is commissioned now
  that the low-level layers are complete; see §15.**
- No model change, no Mathlib TM2 dependency, no space bounds (the design
  must not *obstruct* a later space story, but proves nothing about space).
  *(The space part is superseded in practice: §12's R3 rows and every later
  framed contract carry space or head-envelope clauses.)*
- No retroactive migration of audited epoch-1/2 proofs (see §8).

## 2. Architecture

Three layers over the existing run calculus:

```
Layer 2  CONTROL      timed cond · loop · capture/silence · halt-redirect
Layer 1  PRIMITIVES   named machines with ComputesFunInTime specs, ABI-compliant
Layer 0  (exists)     run calculus · bufferedCompTM/computesFunInTime_comp ·
                      bufferTape/virtualMove relocation · DecidesInTime
Consumer EXISTENTIAL  PolyTimeComputable / ∈ P corollaries only
```

**Design rule (the bridge lesson).** Constructive layers export *named*
`def` machines plus spec theorems; existential packaging (`∃ M c, …`)
appears only at the consumer layer. Quantifier shape is where audits bite —
a consumer may never need to bound an existential witness.

**Composition stance.** The default sequencing mechanism is *whole-machine*
composition via the public `bufferedCompTM` (already proved, `c = 2`
overhead): chain function machines, don't hand-build phase transitions. The
epoch-2 agents could not do this only because (i) the component machines
didn't exist, (ii) branching has no timed combinator, (iii) loops have no
combinator at all. The library supplies exactly (i)–(iii) and otherwise
stops people from proving phase compositions by hand.

## 3. The calling convention (ABI)

The model already gives whole machines a clean boundary: read-only input
tape, `k` work tapes, write-only (append-only) output tape, start at
`initCfg` with blank work tapes. The ABI therefore governs the only places
where configurations cross a seam *inside* a construction: round boundaries
of the loop combinator and entry/exit of wrapped subroutines.

**Canonical configuration** (the single formal notion, defined once):

- designated *state tapes* hold the round data (specified contents, heads at
  origin);
- all *scratch tapes* are blank with heads at origin;
- the output is empty (nothing emitted yet);
- the control state is a designated live anchor.

Loop bodies and wrappers prove "canonical-in ⟹ canonical-out" lemmas; the
combinators own everything else (startup from `initCfg`, final emission,
fuel exhaustion). Proposed discipline for scratch: **the body restores its
own scratch to blank as part of its contract** (it knows its own footprint,
so the proof is its own invariant run backwards), supported by a generic
`clearTM` primitive that sweeps a length-`m` region in `2m + 2` steps.
Rationale: 2A's killer was a *generic* reset proof; a body-specific restore
is mechanical. The alternative (combinator-driven clearing bounded by the
visited-region lemma in `Sweep.lean`) is recorded as the fallback if
body-restore proves heavier than expected. **[Open decision 9.2]**

**Multi-argument functions.** The ABI for arity > 1 is the existing
`pairEncode` idiom; the codec machines (§4) make it mechanical. No tuple
tapes, no new conventions.

**Deciders.** A decider is a function machine emitting the singleton
indicator (`[true]`/`[false]`), i.e. `DecidesInTime` as it already exists.
The decision layer (§6) builds AND/OR/NOT/guard over that, so `∈ P` goals
decompose without touching configurations.

## 4. Layer 1 — the primitive catalog

Rule of admission: a primitive enters the catalog only with **two named
customers** among the open frontiers (2A controller, 2B `choiceVerifier` +
reverse direction, 2C two verifier memberships, 2D `D-MEM`/`D-WRAP`/`D-EMIT`)
and the E3/E4 briefs. Current cut — 12 entries:

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P1 | `copyTM` | id in `n + 1` | exists (`Composition.lean`) | everywhere |
| P2 | `constTM w` | `fun _ => w` in `\|w\| + 1` | exists | 2D D-EMIT, E4 |
| P3 | `prefixTM w` | `fun x => w ++ x` in `\|w\| + \|x\| + 1` | harvest 2C (promotion already requested) | 2C, 2D D-EMIT |
| P4 | `lengthTM` | `fun x => bits \|x\|` (binary length) | new (2D's counter composition is the engine) | 2B, 2C, 2D D-MEM |
| P5 | `polyEvalTM C c` | `fun x => bits (C·(\|x\|+1)^c)` and unary variant | harvest 2D (`polyUnaryTM` + counter) | 2A startup, 2B, 2C |
| P6 | `pairSplitTM` / `pairJoinTM` | the `pairEncode` codec, both directions | new over existing grammar lemmas (2C/2D parsers are drafts) | 2C, 2D D-MEM/D-WRAP, E4 |
| P7 | `replicateTM` | `fun x => List.replicate (f \|x\|) true` for emitted-count `f` | harvest 2D emission chains | 2D D-EMIT, E4 ledger |
| P8 | `compareTM` | equality / `≤` test of two encoded numbers, singleton verdict | new (small) | 2B, 2C bound re-check |
| P9 | `scanLastTM` | split at last `true` (strip discipline), failure verdict | harvest 2C (`stripCertificate` semantics are proved; machine is new) | 2C, 2B split search |
| P10 | `searchTM` | least `i ≤ n` with `p i`, for `p` decided by a supplied decider on encoded `i` | new (uses W1 + loop L) | 2B split, 2C split |
| P11 | `incrementTM` | fixed-width binary increment + overflow flag + rewind | harvest 2A (`enumCarryTM`) | 2A, E3 padding counters, ch3 |
| P12 | `clearTM` | blank a length-`m` region, `2m + 2` steps | new (trivial) | loop bodies, 2A reset |

Each entry ships as: named `def` + one `ComputesFunInTime`/`DecidesInTime`
spec + an ABI-compliance lemma (canonical-out where applicable). Internal
idiom: TM1-style labelled control (a small inductive of labelled phases with
a `step` match), which is what 2D's `PolyControl` was reaching for.

Harvesting means **reimplementation against the ABI with the original proof
as the template** — the audited originals stay untouched in place; see §8.

## 5. Layer 2 — control

**W1. `captureTM` (silence/capture wrapper).** Given machine `D`: run `D`
with every emission suppressed and recorded — core variant records the full
output on a dedicated capture tape; register corollary extracts the first
bit for deciders. Spec: configuration-preserving lockstep, emission on the
halting transition included (the trap every private build re-proved), return
within `T_D + 1` into a live dispatch state, physical output empty.
Consolidates all four private incarnations; the obligations are already
enumerated by the phase-1 and phase-4 audit tables. **[Open decision 9.3 on
variants]**

**W2. `haltRedirectTM`.** 2C's `acceptTM` pattern as a named transformation:
halt iff captured bit is `b`, else enter the one-state live loop (with its
two-line non-halting lemma). Customers: 2A overflow wiring, HALT-style
control modifications, ch3 diagonalization.

**W3. `condTM` (timed branch).** The timed version of `exists_cond`: given
decider `D` (time `T_D`) and machines `M₁, M₂` (times `T₁, T₂`), a named
machine computing `if p x then f₁ x else f₂ x` within
`c · (T_D + max T₁ T₂ + overhead)`. Engine: W1 + the existing private
capture machinery of `Composition.lean`, made public and timed. Customers:
2C/2D reject-on-malformed guards, every parser.

**L. `loopTM` (the centerpiece — bounded loop with tape-resident state).**
Interface factored from 2A's admitted `enumMachine_contracts`, which is the
validated draft:

```
-- SHAPE ONLY. Final quantifiers to be fixed at spec time, audited.
structure LoopSpec where
  (round data σ, encoded on the state tapes; canonical config family cfg : σ → Cfg)
  (body B; fuel R : ℕ → ℕ; per-round budget T : ℕ → ℕ)
  contract : ∀ s, canonical s →
    within T n, B either EMITS a final verdict and halts,
    or reaches canonical (next s)      -- accept-or-advance
  exhaustion : after R n rounds without emission, halted rejection

theorem loopTM_decides …  :
  (loop machine) decides/computes … within
    startup + R n · (T n + c) + c'
```

The combinator owns: startup from `initCfg` (via an init machine composed
with `bufferedCompTM`), the fuel countdown (P11 as the engine), the final
rejection, and the summation. The body owns: accept-or-advance and its own
scratch restore (§3). 2A's proved `enumLoop_run` is the summation lemma's
template; `enumMachine_contracts` then becomes a *library instantiation*
rather than a bespoke admission. Customers: 2A (directly), P10, 2B reverse
direction, E3 padding, E4 stage loops, ch3 clocked simulation.

**Explicitly deferred from layer 2:** a general tape-embedding transformation
(run a `k`-tape machine on a tape subset of a larger machine). The wrappers
and the loop internally preserve "retained tapes" the way 2A/2B already do;
if a third site needs the general form, it gets designed then — not
speculatively now.

## 6. Decision layer (consumer-facing)

Over `DecidesInTime`: negation, conjunction/disjunction (W1-composition),
`guard` (W3 with constant-reject branch), `decideOfFun` (function machine +
P8-style final test), and the `∈ P` glue through the existing
`mem_P_of_dtime_le`/`mem_P_iff`. Everything here is existential and cheap;
its purpose is that goals like `pairedVerifier C c V ∈ P` decompose into
catalog calls plus the semantic lemmas the agents already proved.

## 7. Placement, naming, policy

- New subdirectory `TCSlib/Complexity/TuringMachine/Build/` (precedent:
  `Robustness/`): `Convention.lean` (ABI notions + canonical-config lemmas),
  `Primitives.lean` (P1–P12; split if the 600-line target demands),
  `Wrappers.lean` (W1–W3), `Loop.lean` (L). Namespace `Turing.FinTM`
  throughout (no new namespace).
- Order list: insert after `Simulation`/`Composition`/`Sweep`, before
  `Encoding` — the library depends only on the run calculus and the public
  relocation/composition machinery; nothing Chapter-1-headline depends on it
  (no import cycles, Chapter-1 statements untouched).
- Attribution: standard constructions, tagged [AB09 §1.2–1.4] where the text
  has them (claim-by-claim as policy requires); module docstring records the
  TM1 statement-language idiom as a design reference (Mathlib) alongside the
  Asperti–Ricciotti and Forster–Kunze precedents.
- This is frozen Chapter-1 surface growth → it gets its own audit (§9.4 for
  the vehicle). Spec statements land sorried first (statement-phase
  discipline), the pack leads with the quantifier shapes (ABI, W1 lockstep,
  L's contract) since that is where this design can be wrong.

## 8. Harvest and migration policy

- Harvest = reimplement against the ABI using the original proof as
  template. Originals (2A/2B/2C/2D privates, audited epoch-1 material) stay
  byte-identical; no re-audit of closed work. **Lifted for the foundation
  migration (user, 2026-10-12): see §16.** Migrated files are rewritten, with a
  freeze check, a replay and a gate for each change.
- Deduplication (retiring privates in favor of library calls) is an **E5
  closure task**, recorded in the backlog, not done opportunistically.
- 2C's pending shared-lemma requests (`prefixTM`/`fixedPair`) are subsumed
  by P3 + P6 and get their disposition in this design's audit round.

## 9. Decisions (resolved by the user, 2026-10-03)

1. **Primitive cut** (§4): P1–P12 confirmed as listed.
2. **Scratch discipline** (§3): body-restores-scratch, with
   combinator-driven clearing via the visited-region bound recorded as the
   fallback if body-restore proves heavier than expected.
3. **Capture variants** (§5 W1): tape-capture core + register corollary.
4. **Audit vehicle**: one shared infrastructure round carrying the library
   spec layer *and* the Chapter-1 bridge export.
5. **Build sequencing**: campaign structure — maintainer writes the spec
   layer serially (quantifier-sensitive), shared audit round, then fills
   dispatched as harvest-adaptation batches, the loop fill flagged for
   continuation budget.
6. **Naming**: `Build/` and the P/W/L working names stand; any rename
   happens before the spec audit (renames after it are drift).

## 9a. Spec-phase refinements (2026-10-03, recorded when the spec layer landed)

The spec layer (`TuringMachine/Build/{Convention,Wrappers,Loop,Primitives}.lean`)
realizes the catalog with these refinements against §4–§5, none touching the
frozen §9 decisions:

- **Seam notion**: `Cfg.ofWords` is a *constructor* (anchor state, input head
  at 1, word-per-tape from the origin via `bufferTape`, heads at origin,
  empty output) and seam contracts are `runFrom`-equations against it —
  rewrite-friendly, and `initCfg` is provably the empty-words seam.
- **Packaging**: contracts are existential in the house idiom of
  `Composition.lean`; fills implement named private machines and close them.
  The §2 named-machine rule is realized as quantifier discipline inside each
  statement (machine fixed after its parameters, before all inputs — the
  bridge lesson), not as global naming.
- **P6** is realized as `pairEncodeFixed` (provably an instance of P3 at the
  doubled-word-plus-separator prefix) plus threaded extractors
  `pairFst`/`pairSnd`/`pairValid`.
- **P7** is subsumed by P5's unary clause, whose instances are what the
  emission customers consume. **P8** is realized in threaded form
  (`pairLenCheck` on `pairEncode a b`, so the original input travels with
  the payload and the audited original-bound re-check is against it).
  **P12** has no standalone contract: clearing is intra-machine, part of the
  loop fill's toolkit.
- **W1** is host-parametric (`captureAction`/`captureCfg` transformers + one
  lockstep equation guarded by source liveness), so consumers embed the
  source into their own controller state type; the register corollary is
  derived at fill time. **W2** is the closed `redirectTM` with an
  `Option Bool` last-emission register (`none` = no emission yet; a source
  with empty output never halts the redirect).
- The lint-mandated construction sketches surfaced a real obligation worth
  recording: append-only output means every parser/extractor must **buffer
  until validity is known** — the output-silence discipline reappears at
  the primitive level (extractors, strip, increment's overflow detection).

## 9b. Round-2 repairs (2026-10-03, after `campaign/gates/ch1-infra/findings.md`)

The round-1 audit refuted `exists_loopTM` (blocker: a zero-step identity
"advance" made the hypotheses vacuous while the conclusion violated the
input-head information bound; major: quantifying rounds over *all* state
words at budget `T |x|` excluded the intended customers) and rejected
disposition D5 (missing dynamic assembly and result-bearing search). The
repairs, all in the spec layer:

**The loop contract, redesigned.** Rounds take positive time (`0 < t`);
rounds are required only on words satisfying an input-indexed
admissibility invariant `Inv x s`, established at `s0` and preserved by
the step; and `stepF`/`acceptF`/payload take the input explicitly (the
enumerator's acceptance runs the verifier on `x ++ s`). Two forms:
`exists_loopTM` (Boolean verdict) and the new `exists_loopFindTM` (first
accepting orbit point's payload; `[]` on exhaustion). The countdown sketch
debits from the **second** anchor entry, so `R = 0` still checks `s0 x`
(round-1 finding 4), and the amortized-borrow budget argument was
validated by the auditor.

**Instantiation tables** (the customer-coverage evidence round 1 asked
for; `m n := C·(n+1)^c` abbreviates the certificate-width polynomial):

| Parameter | Enumerator (2A's `enumMachine_contracts`) | Split search (P10) |
|---|---|---|
| `Inv x s` | `s.length = m x.length` | `s.length ≤ x.length + 1` |
| `s0 x` | `List.replicate (m x.length) false` | `[]` |
| `stepF x s` | `(incFixed s).getD s` (stall on overflow keeps the width) | `if s.length ≤ x.length then s ++ [true] else s` (stall keeps `Inv` step-closed) |
| `acceptF x s` | the captured verifier's verdict on `x ++ s` | `s.length + C·(s.length+1)^e = x.length` |
| payload | — (decision form) | `pairEncode (x.take s.length) (x.drop s.length)`, never `[]` |
| `R n` | `2^(m n) − 1` | `n` |
| fuel bits | `Nat.bits (2^(m n) − 1) = replicate (m n) true` — writable within `T` | `Nat.bits n` — writable within `T` |
| orbit, `i ≤ R n` | all `2^(m n)` width-`m` words, each once (`incFixed` enumeration; the stall is beyond fuel) | the candidates `0, …, n` in unary; `find?` = `solveSplit`'s least solution |
| conclusion shape | `[decide (∃ u, u.length = m n ∧ verifier accepts x ++ u)]` | exactly P10's stated function |

Both invariants bound the state-word length by the input, which is
precisely what dissolves the round-1 finding-2 obstruction (no body is
asked to transform words longer than its budget can traverse).

**Catalog additions** (finding 3): P13 `pairConcat`
(`pairEncode x u ↦ x ++ u`, the D-WRAP shape), P14 `pairDup`
(`x ↦ pairEncode x x`), and the combinator C1 `pairMapSnd` (transform a
pair's payload, retain its head; the data-retaining assembly sequential
composition cannot provide). D-EMIT's nested quadruple then factors as
`pairEncodeFixed α₀ ∘ pairMapSnd (unary-runs generator) ∘ pairDup`, and
D-MEM's parser chains through the extractors with `pairMapSnd` carrying
retained components. **P10 narrowing recorded**: the implemented search is
the fixed length-equation search, not the catalog's supplied-predicate
search; the general form is `exists_loopFindTM` itself.

## 9c. Round-3 repairs (2026-10-03, after `campaign/gates/ch1-infra/findings-r2.md`)

Round 2 passed the redesigned loops, P13/P14/C1, and the §9b tables, and
discharged both round-1 refutations; its one major (finding 1) showed the
loop's *final-answer* conclusion cannot discharge the frozen
`enumMachine_contracts`, which is a *configuration-level* contract — the
auditor's delay machine answers correctly yet violates every per-round
bound. Repairs:

**The configuration-level export.** `exists_loopCfgTM` (same hypotheses
as the decision form) concludes with the host's round-configuration
family: startup ≤ `c·(T+1)` reaching `cfg 0`, empty output at rounds
`0…R`, per-round accept-or-advance segments each within `c·(T+1)`, and
the halted `[false]` terminal at index `R+1`. The decision form becomes a
fill-time corollary through an already-halted-terminal summation lemma
plus monotonicity (R3-1: the frozen `loop_run` requires an empty-output
terminal, so it is not invoked directly on the exported family). **Index/budget
translation to `enumMachine_contracts`** (under the §9b enumerator
instantiation, `w := m n`): candidates `2^w = R n + 1`, so the terminal
index matches; the customer's uniform bound `b·(n + w + 1)^e` dominates
`c·(T n + 1)` once `T` is chosen as a polynomial in `n + w` and `b, e`
absorb `c` and its degree; the per-round indicator matches via the fill's
orbit bridge `(stepF x)^[i] (s0 x) = enumWord w i` (little-endian rank
enumeration, `incFixed` = `enumInc` per the round-2 vocabulary note).

**Vocabulary coefficient shift (round-2 note 5, adopted).** The proved
equalities are `splitAtLastTrue = stripCertificate`, `incFixed = enumInc`,
and `solveSplit (C+1) c = certificateSplit C c` — the split-search
equality is false without the shift (R3-3 corrected this pointer). Consequently the padded-verifier pipeline uses P10 at
`(C + 1, c)` while P8 keeps `(C, c)` for the original witness bound.

**General pairing assembly (round-2 item 10's derivation, adopted
verbatim as the canonical recipe).** For computed `f, g`:
`H x := pairEncode (f x) []` (P14 + C1 at the constant-empty function);
`s x := pairEncode x (H x)`; `t x := pairEncode (s x) (g x)` (P14 + C1,
the second with `g ∘ pairFst`); then
`pairSnd (pairConcat (t x)) = pairEncode (f x) (g x)` — the
self-delimiting grammar makes concatenation-into-payload well-formed at
every stage. A C1 call on `pairEncode a b` computes `g b` only; any
cross-component operation goes through this retained-whole-request
pattern, never through C1 directly (round-2 item 10's D-MEM caveat).

**D5 scope (round-2 items 6/10).** The disposition is re-issued for the
epoch-2 frontiers and P10 only; the E3/E4 rows are component-level
plausibility and their full coverage check is deferred to those epochs'
brief audits, where the six-stage/boundary/ledger tables are in scope.

## 10. Cost and sequencing (estimate, campaign points)

| Work | Est. | Note |
|---|---|---|
| Spec layer (all signatures + ABI) | 8 | maintainer, serial; the design-sensitive part |
| Spec audit round | — | rides with bridge export per 9.4 |
| P1–P12 fills | 14 | mostly harvest-adaptation; parallelizable |
| W1–W3 fills | 9 | W1 obligations already tabulated by past audits |
| L fill | 13 | the real risk concentration; continuation budget anticipated |
| **Total** | **≈ 44** | one mid-size batch equivalent |

Sequencing: freeze this design → spec statements + bridge export → shared
audit round → fills → **then** E2 continuation briefs, which cite the
library instead of re-deriving machines. E2 continuations, E3, E4, and the
ch3 skeleton are the customers that pay this back; the loop combinator is
the piece to watch for slippage.

## 11. The emitter increment (proposed 2026-10-05, post-E3 integration)

**Evidence.** E3's outcome maps the library boundary exactly: everything
recognizer-shaped closed in one round through the catalog (3B's memberships
via `computesFunInTime_splitSolve 1 1` + capture + the audited wrappers; 3D
via P10 + capture + composition), while both stalls sit on the producer
side — 3B at a streaming transducer (`satRedTM` states 9–34, defined,
unproved), 3A at a loop body that must internally run an evaluator and emit
a payload, over a width family the catalog's split instance doesn't cover.
The loop contracts deliberately require **empty output through every round**
(round-2/3 audit repairs), and composition offers only input-pipelining —
there is no output-append mode anywhere in the library. E4's summit
(`SAT_NPHard`, 15 pts, continuation certain) is an emitter of exactly this
shape: a per-index loop appending clause groups under the six-stage
output-silence contract with an exact serialization-length ledger.

**Rule of admission check** (§4): every item below has at least two named
customers among 3B-cont, 4A, 4B, and 3A-cont.

### E1. `emitLoop` — the emitting loop (control layer)

The loop engine's output clause generalized: rounds append exact per-round
emissions instead of staying silent. Shape (final quantifiers at spec time,
audited):

```
-- SHAPE ONLY. Sibling of exists_loopCfgTM, sharing its host machinery.
Inv, s0, stepF as in the decision loop; additionally
  emitF : input → σ → List Bool        -- the exact chunk of round i
contract: startup ≤ c(T+1); per-round segments ≤ c(T+1); positive
  first-return; for every i ≤ R:
    (cfg i).output = (List.range i).flatMap (fun j => emitF x (stepF^[j] s0))
  terminal: halted, output = the full concatenation (no verdict bit — the
  machine COMPUTES the concatenation; a deciding variant is NOT included).
```

Body obligations unchanged (accept-or-advance becomes advance-and-emit;
scratch restore per §3/9.2). The summation lemma is `loop_run`'s template
with the output clause threaded. **Customers:** 4A (the per-snapshot clause
emitter — the design driver), 3B-cont (`satRedTM`'s streaming core as an
instantiation), 4B (dual reduction emitter).

### E2. `emitPhase` — the forwarding wrapper (control layer)

The dual of W1: run an embedded transducer `T` (a `ComputesFunInTime`
contract) inside a host, with `T`'s emissions landing on the **host's**
output tape, source tapes isolated, halt redirected to a live return state;
lockstep lemma in `capture_run`'s mold with "physical output = host prefix
++ T's output so far". This is what lets a catalog transducer serve as one
emission stage of a larger machine — today's only option is whole-machine
input-pipelining. **Customers:** E1's per-round chunk calls (4A emits each
clause group through a sub-transducer), 3B-cont (fresh-literal chain
emission), 3A-cont marginally (the success payload `pairEncode` emission).

### E3′. Stream primitives (catalog rows P16–P18)

| # | Primitive | Spec (shape) | Source | Customers |
|---|---|---|---|---|
| P16 | `tokenStepTM` | consume one self-delimiting token (unary index / marker) from the input head, land head after it, expose the token in control | harvest: 3B's proved `satScanTM`/`satSyntaxStep`, 3D's six-state scan, 2D's parsers (fourth re-derivation otherwise) | 3B-cont, 4A, 4B |
| P17 | `chunkEmitTM w` / parametric | append a control-determined word to output, `\|w\|` steps, no tape movement | new (trivial); the per-token emission atom | E1 bodies, 4A |
| P18 | `unaryAccTM` | dedicated-tape unary accumulator: append one, read-length-in-binary via P4 composition, rewind | harvest: 3B's proved counter stages (`satRedCounter_write`, `satRed_maxOnes`, startup to state 9) | 3B-cont, 4A fresh indices |

### E4′. `splitSolveWith` — width-parametric split search (control layer)

Generalize P15's split search from the hardwired polynomial family to a
hypothesis-supplied width evaluator: given a machine `E` with a captured
`ComputesFunInTime (fun s => bits (f s.length)) T_E` contract and
monotonicity of `n ↦ n + f n`, a machine solving `n + f n = m` (first
success payload `pairEncode (take n) (drop n)`, exhaustion verdict) within
the loopFind envelope over `T_E`. **Harvest source:** 3A-cont's bespoke
body, whose contracts are already displayed in its REPORT — build the
parametric form against that template once it lands (or directly, if this
increment executes first). **Customers:** 3A-cont's equation (plug the
proved `e3_exp_bits_timed`), every future padding argument (ch3+ time
hierarchy pads the same way).

### Placement, cost, open decisions

- **Placement:** E1 extends `Loop.lean` **in-file** to reuse the audited
  `loopHost` privates (a separate `Build/Emit.lean` cannot see them — the
  D7 cross-file-privates qualification; re-deriving the host would be a
  second 2,500-line proof). `Loop.lean`'s size exception grows and the D7
  split trails as already recorded. E2 joins `Wrappers.lean`; P16–P18 join
  `Primitives.lean`; E4′ joins `Loop.lean` beside P15's engine.
- **Non-goals:** no deciding variant of the emitting loop (compose E1 with
  the existing decision layer instead); no general transducer algebra; no
  speculative tape-embedding (unchanged from §5's deferral).
- **Cost estimate:** spec layer 4; one shared-infra audit round (the ch1
  pattern, expected lighter — one host extension, not a new host); fills:
  E1 8, E2 4, P16–P18 5, E4′ 6 — **≈ 27 points**, roughly the L batch.
- **Sequencing:** freeze this section → spec statements → audit round →
  fills → 3B-cont consumes E1/E2/P16–P18; 4A's brief cites the layer
  instead of a bespoke emitter. **3A-cont dispatches in parallel, bespoke**
  (disjoint ownership; its body becomes E4′'s harvest template; later
  dedup is a recorded E5-style maintainer task, never the fill's).
- **Open decisions (user):** (11.1) approve the increment and this scope;
  (11.2) E1 as a sibling contract beside `exists_loopCfgTM` (recommended)
  vs a generalization replacing it (touches audited statements — not
  recommended); (11.3) whether 4A's brief waits for this gate to close
  (recommended) or anticipates it.

## 11a. Spec-phase refinements (2026-10-05, recorded when the emitter spec landed)

Decisions 11.1–11.3 resolved by the user (2026-10-05): increment approved;
E1 is a **sibling** contract beside `exists_loopCfgTM` (no audited statement
is generalized or touched); 4A's brief **waits** for this gate.

Refinements against §11 as drafted, all narrowing:

1. **P17 is subsumed** (no new statement): a constant chunk emission is
   `emitPhase` (E2) applied to the existing P2 `constTM` — recorded here
   the way D4 recorded the prefix/fixed-pair subsumptions.
   *[Superseded by §11b item 6 and §11c: the discharging rule is body
   finite control for fixed words, or `exists_emitCallTM` for computed
   chunks — never the private `constTM` (round-2 audit, finding 3).]*
2. **P18 narrowed to `computesFunInTime_appendBit`**: the drafted
   accumulator row conflated the append atom with cross-phase persistence,
   and persistence is already the loop engine's state-word mechanism; the
   catalog takes only the atom.
3. **E4′ lives in `Primitives.lean`**, not `Loop.lean`: its conclusion
   speaks `pairEncode`, which `Loop.lean` does not import, and P15's own
   public contract already lives there — the engine/contract split follows
   P15 exactly. Its pure vocabulary `solveSplitWith` joins `Convention.lean`
   beside `solveSplit`, which it definitionally generalizes.
4. **E1 is function-level only** (`exists_emitLoopTM` concluding a
   `ComputesFunInTime` of the chunk concatenation): all three named
   customers deliver `PolyTimeComputable` reductions, i.e. function-level
   contracts, and in-host composition of an emitter is E2's job, which
   takes function-level transducers. The round-2 lesson (final-answer vs
   configuration gap) was checked against each customer before choosing
   this form; a configuration-level export would follow the round-3
   precedent if a consumer ever surfaces.
5. **No emission-size hypothesis on E1**: the round seam equality itself
   bounds each chunk by the round's duration (output grows by at most one
   symbol per step), so the statement carries no redundant bound to drift.

Spec surface: **five sorried contracts** (`Turing.emit_run`,
`Turing.FinTM.exists_emitLoopTM`,
`Turing.FinTM.computesFunInTime_splitSolveWith`,
`Turing.FinTM.computesFunInTime_unaryToken`,
`Turing.FinTM.computesFunInTime_appendBit`), two real transformers
(`emitAction`, `emitCfg`), two pure vocabulary definitions
(`solveSplitWith`, `unaryTokenSplit`). Convention's module-docstring
vocabulary bullets extend at fill time (append-only).

## 11b. Round-2 repairs (2026-10-05, after `campaign/gates/emitter-infra/findings.md`)

Round 1: **0 blockers, 2 majors, 3 minors** — no false statement among
the five contracts; both majors are adequacy obligations, repaired here.

1. **The clean-call bridge (finding 1, major).** A function-level
   contract cannot deliver the loop seam: a witness may dirty scratch or
   leave heads displaced on its final transition and still compute `f`
   within `T`. Two new sorried bridge contracts supply the
   prepared-input/clean-return interface, both with canonical
   `Cfg.ofWords`/`stateWord` entry **and** exit seams, first-positive-
   visit discipline, and envelopes charged to `T + |arg| + |f arg| + 1`:
   `Turing.FinTM.exists_installCallTM` (result installed as the
   tape-resident word, nothing emitted) and
   `Turing.FinTM.exists_emitCallTM` (argument preserved, the computed
   chunk forwarded to physical output). Both live in `Loop.lean` beside
   the seams they serve (`stateWord` is defined there). Fill route: the
   A-continuation's proved log/undo pattern around the capture wrapper,
   with virtual-input preparation from the tape-resident argument.
   `emitCfg`'s docstring now states explicitly that it does not
   normalize terminal configurations — the bridges do.
2. **The 3B normalization mapping (finding 1, required resolution).**
   The reported `satRedTM` is **not** the promised instantiation as it
   stands (its permanent position-−1 marker contradicts the blank
   `ofWords` seam; its raw head positions cannot cross seams). The
   committed instantiation plan: loop state word encodes
   `(cursor, consumed-prefix length, phase tag)` via the audited pairing
   vocabulary — the raw streaming position is re-derived each round by
   advancing past the consumed prefix, and **the permanent marker is
   eliminated** (round-local buffering restores its tape by round end).
   Per round: decode the state word; `exists_installCallTM` over
   `computesFunInTime_unaryToken` reads the next token of the remaining
   serialization; finite control classifies marker/polarity bits; the
   emitted clause fragment goes out through `exists_emitCallTM` (chunks
   are of token-bounded length) or directly by finite control for
   fixed fragments; the fresh-variable counter updates through
   `computesFunInTime_appendBit` + install. Rounds have positive
   duration and input-length-only budget; `R` = the serialized input
   length (each round consumes at least one input position); once the
   formula terminator is consumed, an **absorbing finished phase emits
   empty chunks** for all remaining rounds. Token output is decoded by
   `pairDecode`-side vocabulary (proved); append output becomes the
   next state word by the install call. The banked `satReduction_*`
   semantics close the function identity; `satRed_start`'s proved
   maximum-pass survives as the `s0` computation.
3. **The 4A stage mapping (finding 2, required resolution — recorded
   here, certified against the attached phase-4 records in round 2).**
   All-string validation runs **before any irreversible emission**: the
   validation stages run as a decision prefix (the audited conditional
   W3 over the parser/boundary checks); only the valid branch enters
   the emitting loop, and the invalid branch emits the fixed fallback
   through finite control. Logical round count: `R` = the
   snapshot-index bound of the six-stage contract (an input-length-only
   polynomial), one clause group per round through `exists_emitCallTM`;
   the exact serialization-length ledger is the sum of the per-round
   chunk lengths — never constant-per-clause, exactly as the phase-4
   ledger demands. Serialization terminators: the final terminator is
   the last round's chunk tail (or a post-loop constant emission by
   finite control); both options keep the concatenation exact.
4. **Host routing correction (finding 3, minor).**
   `exists_emitLoopTM`'s construction sketch now specifies the
   **forwarding host variant** (body dispatched through `emitAction`;
   fuel/countdown machinery reused; contracts proved over
   arbitrary-accumulated-output configurations; a **new**
   prefix-summation lemma modeled on `loop_run`) — the unchanged
   find-mode host is refuted by the auditor's one-state witness, since
   `captureAction` suppresses the body's physical output.
5. **Token conventions (finding 4, minor).** `unaryTokenSplit`'s
   docstring now states it consumes unary tokens only, with the
   auditor's separating example; standalone markers and polarity bits
   are scanner grammar states.
6. **P17's actual rule (finding 1's visibility note).** Fixed
   finite-control chunks are emitted directly by body control (no
   primitive, no appeal to the private `constTM`); unbounded
   tape-dependent chunks go through `exists_emitCallTM`. §11a item 1 is
   corrected accordingly: the subsumption's discharging rule is body
   finite control, or the emit call, never the private constant
   machine.
7. **Documentation (finding 5, minor).** The four definitions now carry
   customers and construction notes; attestation 4's "every new
   declaration" claim is restated in the round-2 pack as exactly what
   each class of declaration carries.

Spec surface after round 2: **seven sorried contracts** (round 1's five
plus the two bridges), two transformers, two vocabulary definitions.

## 11c. Round-3 repairs (2026-10-05, after `campaign/gates/emitter-infra/findings-r2.md`)

Round 2: **0 blockers, 2 majors, 1 minor** — round-1 findings 3–5 closed;
the bridge construction and the 3B normalization validated (r2 findings
4–5, including a 5,908-case finite corroboration of the normalized
schedule); the two cumulative majors repaired here.

1. **Positive tape count on both bridges (r2 finding 1, major).** At
   `C.k = 0`, `stateWord 0 a = stateWord 0 b` by empty domain, so the
   install conclusion was satisfiable by a two-state zero-tape machine
   for an arbitrary — even noncomputable — `f`: vacuous as a data
   interface. Both conclusions now carry `0 < C.k`, making the seam
   equality yield the genuine `bufferTape` content at index zero. The
   auditor's r2 finding 4 confirms the log/undo construction delivers
   the strengthened interface at the stated envelope.
2. **The 4A mapping rewritten (r2 finding 2, major) — this supersedes
   §11b item 3 in full.** §11b item 3 wrongly substituted parser
   validation for Cook–Levin's silent preparation stages: the 4A source
   is an arbitrary `NP` language, every binary word is a legitimate
   instance, and there is no CNF well-formedness condition on `x` (the
   auditor's empty-language witness: validation-plus-fallback would
   emit the satisfiable `serialize [] = [false]` for a no-instance).
   Parse-before-emission belongs to the 3B/4B decode-based transducers
   only. The corrected stage-to-seam mapping:
   - **Silent preparation (inherited stages s1–s5).** A silent startup
     phase computes and packs the preparation records into `s0 x`:
     exact `Q(n)`, `m = n + Q(n)`, and the horizon `T` (s1, exact
     arithmetic, certificate length never enlarged); the virtual
     reference input `false^m` with clamped virtual head, source
     writes/moves executed on the halting transition, source output
     suppressed and halt internalized (s2–s3, through the capture and
     install-call interfaces at positive tape count); the inclusive
     trajectory records for **all** times `0..T` with administrative
     transitions outside simulated time and frozen positions after an
     early halt (s4); greatest-strictly-earlier-visit records with
     sequential comparison costs (s5). All of s1–s5 end with empty
     physical output and the packed records as the clean persistent
     word — the emitting loop's `s0`.
   - **Ordered emission (s6).** One **family member per round**, the
     cursor walking the fixed family order of the phase-4 contract.
     With `T + 1` snapshot times and `k` work tapes, the six families
     have `n, 1, T, T+1, k(T+1), T` members; the round count is their
     sum: `R = n + (k+3)·T + k + 1` (an input-length-only polynomial).
     Rounds with empty template output still take positive time. The
     single final formula terminator is appended to the last round's
     chunk. The serialization-length ledger is the exact sum
     `1 + 2·#clauses + Σ (v+3)` over literal occurrences — total
     output `O_M(T²)`, never constant-per-clause.
   - The alternative `R = T` time-major grouping is **not** adopted:
     it would need a separate proof that its interleaving reserializes
     to the fixed family order.
   Certification of this mapping against the phase-4 round-2
   boundary-check table is round 3's business — that table
   (`campaign/gates/ch2-phase4-reaudit/findings.md`) rides in the r3 bundle,
   and the 4A brief inherits it verbatim per the standing rule.
3. **P17 cross-reference (r2 finding 3, minor).** §11a item 1 now
   carries an explicit supersession marker pointing at §11b item 6;
   the historical text is preserved as history.
4. **Provenance upgrades for round 3.** The log/undo fill route now has
   fresh in-repo provenance beyond the epoch-2 enumerator: the
   A-continuation checkpoint (integrated 2026-10-05) banked exactly the
   track/clear/compare phase family the r2 finding-4 construction
   describes (`e3cTrackTM`/`e3c_track_run`/`e3cClearTM`/`e3c_clear_run`
   — logged simulation over a visited interval with origin markers,
   exact single-triple cleanup at `6T+7`, positive first returns), as
   proved privates in `Nondeterminism.lean`; its REPORT and source ride
   in the r3 bundle.

Spec surface after round 3: unchanged in count — **seven sorried
contracts** (the two bridges now carrying `0 < C.k`), two transformers,
two vocabulary definitions.

## 11d. Gate close (2026-10-05, after `campaign/gates/emitter-infra/findings-r3.md`)

Round 3: **0 blockers, 0 majors, 1 minor, 4 notes — GATE CLOSED**
(`campaign/gates/emitter-infra/resolutions.md`). Both cumulative majors
discharged: the positive-tape bridges export the data interface (the
auditor's projection-table derivation), and §11c's 4A mapping is
certified against the inherited boundary table, including the exact
per-member chunk rule. The minor — swept in the closing commit — was an
attribution error of §11b item 1/§11c item 4 and the install-call
sketch: the A-continuation's delivered provenance is
**visited-interval tracking and clearing** (`e3cTrackTM`/`e3cClearTM`),
not an overwritten-symbol history/undo implementation; at a clean
entry seam, clearing is restoring, so the track/clear route fills the
bridges directly, and history/undo stands only as the independently
derived alternative (r2 finding 4). Two clarifications from r3
finding 3 bind the 4A brief: `R = n+(k+3)T+k+1` is the last round
index (member count `R + 1`), and the chunk rule emits per-member
flatMaps with the single terminator on the last chunk only. Fill
batches proceed under the resolutions' binding section, partitioned
Loop / Primitives / Wrappers.

## 12. The routine layer (proposed 2026-10-08, pre-ch3/4 campaign)

**Mandate** (user decisions 2026-10-06 and 2026-10-08, recorded in `backlog.md` §2
and `AroraBarakChapters3-4Plan.md` §4a/§8): built after the Chapter-2 closure and
**before the chapter-3/4 fill epochs**, in parallel with their statement phases;
scoped to **amply support the chapter-1/2 retrofit**, not merely the new
consumers; and — superseding §1's "no space bounds" non-goal for this increment —
**every item below carries a space clause alongside its time cost**, so that the
chapter-4 campaign and the P4.x statements consume the layer without a second
pass. The space measure is the house one: `Turing.MultiTapeTM.spaceUsed`
(work-tape cells visited; input and output tapes excluded).

**Evidence.** The 4A chain is the measurement: roughly half of the A2/A3
deliveries' 202 native privates are hand-rebuilt bank/relocation/dispatch
routines; the `emitterBank*`/`emitterP2*` relocation family was privately
re-harvested three times; and A3's proved costs (`3|w| + 3` copy, `2|w| + 2`
clear) match the external prior art's `3w + 2`/`2w + 2` to within one step —
independent convergence on the same catalog, discovered in the 2026-10-06
survey. The emitter round-1 finding stands: *function-level* contracts cannot
deliver clean-return seams, so the gap is configuration-level. §5 deferred the
general tape-embedding transformation "until a third site needs it"; the third,
fourth, and fifth sites have now arrived (the retrofit families, the
Hennie-Stearns conversion, the two-work-tape universal machine).

**What already exists and is consumed, not duplicated** (colleague modules,
Hydroxyi/Jason Dong, on `main` since `f70c57c2`): the *function-level half* —
`TuringMachine/CounterProg{,Run}.lean` (goto programs over unary registers
compiled once into `FinTM`, `t` abstract steps within `t(2t+3)` machine steps,
FP bridge via `ClassNP/CounterProgPolyTime.lean`), `ClassNP/Transducer.lean`,
`ClassNP/{PolyTimePairing,PClosure}.lean`, `TuringMachine/UnaryTape.lean`; and,
on the space side, `SpaceComplexity/Machines/` (the `LogProg` register-program
compiler with `compile_space`/`arm_decides`). §12 supplies the
configuration-level half those layers sit on.

### R1. Bank embedding (the §5 deferral, promoted)

A verified routine on its own `m`-tape set runs on any injectively selected
subset of a `k`-tape host's work tapes, cost unchanged, everything else framed.
Spec shape (final quantifiers fixed at spec time, audited): for an embedding
`ι : Fin m ↪ Fin k`, transported actions and configurations with

* **lockstep** — transported `runFrom` commutes with the source `runFrom`;
* **frame** — tapes outside `range ι` are byte-identical before and after, their
  heads unmoved; input position tracks the source; emission policy is a
  parameter (suppressed or forwarded — the W1/E2 pair fixes the two modes;
  whether this is one transformer with a mode or two transformers is open
  decision 12.4);
* **time** — step count preserved exactly;
* **space** — cells visited on host tape `ι i` equal cells visited on source
  tape `i`; unselected tapes visit nothing new.

Generic form of: `emitterBank*`, the `emitterP2*` relocation family,
`clBank*`/`clSlot*` (4A chain), and their chapter-1 analogues in
`Build/Primitives.lean`/`Build/Loop.lean` internals.

### R2. Seam composition

Sequential composition of two controllers at a canonical `Turing.Cfg.ofWords`
seam (Convention.lean's ABI notion): if `M₁` carries seam `c₀` to seam `c₁`
within `T₁` under a first-return cut, and `M₂` carries `c₁` to `c₂` within
`T₂`, the dispatch-glued machine carries `c₀` to `c₂` within `T₁ + T₂ + O(1)`,
with the glue state-sum and dispatch lemmas owned by the combinator. Space
clause: visited sets union, so per-tape space is bounded by the sum of the
parts' per-tape spaces (whether the spec states the sharper per-tape `max` for
disjointly-owned tapes is open decision 12.1). Generic form of the per-batch
dispatch gluing re-proved in every A-chain and emitter batch.

### R3. Catalog promotion, with space costs

Promotion of the remaining audited A-chain privates as public machines with
exact time *and* space costs: transfer (word from tape `i` to tape `j`,
`3|w| + 3`), copy (`3|w| + 3`), clear (`2m + 2`, = P12's engine), compare, and
increment — D6-style promotion, not new proof work, seeded from the named
private families. Additionally, the existing catalog rows (P1-P12, P16-P18)
and the W/L/E combinators are **retro-annotated with space theorems** — new
`spaceUsed` lemmas beside the existing specs, no signature changes, so the
audited statement surface is untouched (additive growth; open decision 12.3 on
doing this here versus lazily per consumer — the amply-support mandate argues
for here).

### Consumers (rule-of-admission check, §4: two named customers per item)

| Consumer | Uses |
|---|---|
| Chapter-1/2 retrofit (backlog §2) | R1 for the bank/relocation families; R2 for the dispatch families; R3 for `clCopy*`/`clCmp*`/`clRead*`/`clCount*` and the `Build/` harvest families |
| Hennie-Stearns `k`→2 conversion ([AB09] §1.7; ch3-4 plan §2.1) | zones as banks (R1), shifts as R3 transfers, seam discipline (R2); the amortization is mathematics on top |
| Two-work-tape universal machine (ch3-4 plan §2.1, §4a) | R1 + R2 throughout; the retrofit pilot; candidate space-bounded variant feeding Thm 4.8 / Ex 4.1 |
| Chapter-4 ARM extensions (ch3-4 plan §2.5: nondeterministic and polynomial-width variants of `LogProg`) | R1/R2 at their `FinTM` compilation boundary; R3 space rows |

### Placement, sequencing, cost

* New files `Build/Embed.lean` (R1) and `Build/Seam.lean` (R2); R3's new rows in
  a new `Build/Catalog.lean` (`Primitives.lean` is already over the size policy;
  final name is open decision 12.2, settled before the spec audit per §9.6).
  Namespace `Turing.FinTM`; order list after `Build/Loop`.
* Process per `workflow.md`: maintainer-serial spec layer (quantifier-sensitive,
  as §10), statement gate, fills as harvest-adaptation batches, fill audit. The
  gate must close before the first chapter-3/4 fill epoch (plan §4a); statement
  phases of chapters 3-4 run in parallel.
* Estimate (campaign points): R1 spec+fill ≈ 10 (the lockstep is the risk
  concentration, L-style), R2 ≈ 8, R3 promotions + space retro-annotation ≈ 12,
  serial spec layer ≈ 6. Total ≈ 36, one mid-size batch equivalent.

### Open decisions (human review; audit verifies, never disposes)

* **12.1** R2 space accounting — **answered (user, 2026-10-08): the sharper
  form.** The spec states per-tape bounds, with the max for disjointly-owned
  tapes (sharpest available; downstream applications may depend on the
  sharpness).
* **12.2** R3's file layout — **answered (user, 2026-10-08): option (a)**, a
  new `Build/Catalog.lean` holding the new rows and the space lemmas for the
  old rows, keeping `Primitives.lean` byte-identical (**the byte-identity is
  lifted for the §16 migration, user 2026-10-12**); a backlog item records
  the later refactor toward the symmetrical per-theme layout (option (c)),
  via the D7 split window.
* **12.3** Space retro-annotation — **answered (user, 2026-10-08): the refined
  now-option**: the primitives as realized (P1-P15), wrappers (W1-W3) and the
  loop (L) get `spaceUsed` theorems in this increment; the emitter combinators
  (E1-E4′) stay lazy until a space consumer appears, **and the E3′ stream rows
  P16-P18 ride with that lazy scope** (their only consumers are the emitters —
  scope clarification recorded at skeleton time, 2026-10-08, flagged to the
  §12 statement-gate audit and reversible there if the gate reads the
  original "P1-P18" wording as binding).
* **12.4** R1 emission policy — **answered (user, 2026-10-08): two named
  transformers** (suppressing and forwarding) over a shared private core, so
  each spec stays crisp and downstream applications cite whichever fits.

### Citations (policy.md §2, *Design adaptation*)

The configuration-level design is adapted from — with nothing transcribed —
**Édouard Bonnet's `classical-complexity`** (Lax Archive lax-434930), module
`proofs/Lax434930Proofs/InclusionAux/TimeCompiler/`: `StackProgram`'s
`compile_correct`, `StackRename`'s `rename_executes`/`executes_in_sum` (the
bank-embedding and seam-composition shapes), and the
transfer/clear/copy/for/repeat routine catalog; commit
`0c0840319318215fd7b36a9a822b81ce55cf6941`, Apache-2.0; examined 2026-10-05,
different toolchain (Lean 4.33 vs our 4.25) and machine model (TM2-style keyed
stacks vs `FinTM` tapes with heads). Suggested tag: `[Bon26]`. The R-modules'
docstrings and their blueprint entries must carry this citation, alongside the
existing `[Balbach22]` (AFP `Cook_Levin`) for the composition architecture and
the in-repo credits to the colleague modules named above.

*Historical (2026-10-14).* `NL_subset_P`'s former sketch cited [Bon26] as design context for
S1b's planned BFS (reachability-table construction; nothing ported). The ARM proof in
`SpaceComplexity/ExpTime.lean` (received `8c23f3bc`) neither uses nor adapts it, and its
docstring drops the tag.

### 12.5 Round-1 audit repairs (2026-10-09)

The §12 statement-gate round 1 (`campaign/gates/routine-infra/findings.md`: 0
blockers, 4 majors) drove four repairs, landed with the round-2 pack:

* **R1 → the returning embeddings** `embedSilentRetTM`/`embedEmitRetTM`
  (states `S ⊕ Unit`): the closed transformers lose a final halting
  emission to either the halt or a premature seam dispatch — the audit's
  formal trace. The returning flavors execute every source action through
  the halting transition and land in the live anchor `Sum.inr ()`.
* **R2 → general-configuration seam composition**
  (`seamCompTM_run_ofCfg` + first-return and visited forms): the canonical
  `Cfg.ofWords` theorems cannot consume arbitrary frames, displaced
  inactive heads, or accumulated output; the general form starts phase two
  from phase one's returned configuration with only the control state
  replaced.
* **R3 → the fresh-entry/release adapter** `seamReleaseTM`: positive
  calls returning to their own anchor are now seam-consumable (the entry
  action executes unconditionally from a fresh start state).
* **R4 → the threaded-map witness** is re-commissioned as a forwarding
  controller (validate/buffer, emit prefix, forward payload output);
  the received captured-payload machine is refuted as a witness for the
  linear-administration bound.

Scope notes R9 (physical-tape selection is not zone multiplexing) and R10
(loop sibling contracts not exported) are recorded at their definition
sites.

### 12.6 Framed catalog contracts (2026-10-10, after ZF-A2's escalation)

**The gap.** The R3 rows (`transferTM`, `copyTM`, `clearTM`, `compareTM`,
`incrementTM`) are stated only from `Cfg.ofWords`: every head at the origin,
every tape a globally buffered word. The zone shift machines (`Build/Zone.lean`,
`exists_zoneShiftInTM`/`OutTM`) have **exactly two tapes**. One is the zoned data
tape; the other is a scratch tape that starts and ends as the unary level word.
Their staging, cleanup and binary navigation counter therefore all run at
**displaced heads beside unrelated data**, where no canonical contract applies.

ZF-A2 (`campaign/fills/zone/reports/f1-A2-REPORT.md`) showed the gap concretely,
with a kernel-checked regression. On a valid three-level carrier, a bare transfer
from a displaced head reads past the word's end and erases a cell that belongs
to the next zone. The cure is a delimited word: blanks at relative positions
`-1` and `|w|`, installed by the consumer, which saves the overwritten cells in
finite control and restores them afterwards. Correspondingly, the contract must
quantify over an arbitrary surrounding frame.

**Decision (user, 2026-10-10).** A small §12 extension: maintainer-drafted
statements, a short statement gate, then a fill batch; ZF-A3 follows. The
routines are local, since each step reads only the scanned cells of the touched
tapes, so a framed contract is the faithful generalization. No new machine is
defined.

**The five statements** (`Build/Catalog.lean`, after the R3 rows, sorried):

| Contract | Exact time | Effect on the touched tapes |
|---|---|---|
| `transferTM_run_ofCfg` | `2·|w| + 2` | source interval blank; destination interval `w` (old destination contents arbitrary) |
| `copyTM_run_ofCfg` | `2·|w| + 2` | destination interval `w`; source intact |
| `clearTM_run_ofCfg` | `2·|w| + 2` | the word interval blank |
| `incrementTM_run_succ_ofCfg` | `2·p + 2`, where `p = (w.takeWhile id).length` | the word interval holds `v`, where `incFixed w = some v` |
| `incrementTM_run_overflow_ofCfg` | `2·|w| + 2` | the word interval all `false` |

In every case the routine reaches its `done` anchor exactly at the stated time
and not earlier. Every cell outside the word intervals, every head, the native
input position and the output are unchanged. Up to the exit the touched heads
stay within `[pos − 1, pos + |w|]` (for a successful increment, `[pos − 1,
pos + p]`) and all other heads are fixed. Space bounds follow from the
trajectory clause through `MultiTapeTM.spaceUsedByTape_le_card_Icc`.
`incrementTM`'s carry-sensitive `2p + 2` is the per-step cost that makes the zone
machines' anchored binary countdown sum geometrically, the audited `O(2^i)`
navigation ledger. The canonical `2|w| + 2` public bound is too loose for that,
as ZF-A2 flagged.

**Specialization and dedup.** With the origin heads and globally buffered words
of `Cfg.ofWords`, each framed contract specializes to its canonical R3 row. The
fill batch therefore proves the framed form and **re-derives each canonical row
from it**, through a sanctioned proof-body swap with the public statement
unchanged. That generalizes the private trace lemmas rather than duplicating
them. `compareTM` is not framed here, since no current consumer needs it; it
follows the same pattern on request.

**Pre-ship execution check (mandatory practice).** Every statement was executed
on concrete configurations with displaced heads, a nonblank outer frame and the
edge cases (`w = []`, `p = 0`, all-`true` overflow). The exact final
configuration, the no-earlier-exit clause and the trajectory were compared:
63 cases, all pass, and a wrong-time negative control fails
(`campaign/gates/s12-framed/evidence/`).

### 12.7 Counter-driven loops (design, 2026-10-10, after ZF-B3's escalation; decisions 12.7.1–12.7.6 taken by the user the same day)

**The gap.** ZF-B3 (`campaign/fills/zone/reports/f1-B3-REPORT.md`,
`f1-B3-CONTINUATION.md`) stopped on two shared-interface requests:

- a public fixed-width **decrement** routine with a framed contract;
- a loop whose number of rounds is a **binary counter read from a tape**,
  with the body's state kept on **persistent, arbitrarily positioned tapes**.

Every public loop host (`exists_loopTM`, `exists_loopCfgTM`,
`exists_loopFindTM`, `exists_emitLoopTM`) does something else. It runs
`R x.length` rounds, a count fixed by the input's *length* through a fuel
machine, and every round runs between canonical
`Cfg.ofWords anchor (stateWord …)` seams. A simulator would therefore have to
re-serialize its two simulated work tapes every round, which ZF-B3 rightly
refused.

**This is a shared need, not a ZF-B3 one.**

| Consumer | Status | What it needs |
|---|---|---|
| `Codes2Tape.exists_uniformMachineCode2` | ZF-B3's open target | Simulate at most `t` source steps, `t` in binary on a tape, over two persistent source tapes; one joint polynomial |
| `Diagonalization/EXPCOM.lean` | sorried | The same pattern ("simulate at most `t` source transitions under a binary countdown") |
| `Diagonalization/NTimeHierarchy.lean` | sorried | A **fused** countdown at **linear** overhead: one tick per simulated step, the borrow cost amortized by `Σⱼ ν₂(j) ≤ t` (round-1 finding 5). It needs an **amortized total**, not a per-tick worst case |
| `SpaceComplexity/Hierarchy.lean` | sorried | A configuration-count clock |

**Existing clocks, all private or super-linear.** These are 12.2c candidates
for re-derivation as consumers of the shared host, not inputs to copy:

- `Build/Loop.lean`'s fuel debit: `loopDebit`, `loopValue`, `loopHost_borrow*`.
- `Build/Catalog.lean`'s `f2_loopDebitTM` / `f2_loopBorrow_correct`. This is a
  clean 1-tape little-endian decrement: exact `2·(borrow position) + 2`
  steps, zero wraps to all-`true` with an underflow verdict. It is stated
  only canonically.
- `Universal.lean`'s private deadline interpreter `timedUniversalTM`, the
  quadratic one-tape clock behind `timed_universal`.
- `TimeHierarchy/ClockMachine.lean`'s `clockTM`, the time hierarchy's clock. Its
  specification `clockTM_spec` (`ClockLoop.lean`) is linear in the counter value; "quadratic"
  here was wrong (corrected 2026-10-13, C1 design note): the quadratic bound is
  `timed_universal`'s. These are colleagues' files; under the user's standing preference
  any dedup there is 12.2c work, not theirs.

**Proposed components.**

**C1 — `decrementTM k i : MultiTapeTM k Bool FlagPhase`**, an R3-family row,
the mirror of `incrementTM`. It scans `false` cells to `true` moving right; the
first `true` becomes `false`, with the success verdict; reaching the right
blank, the word is all `false`, so the value is `0`, and the verdict is
underflow, leaving the word all `true`. It returns to the origin through a
`rewind` phase. Framed contracts, in the §12.6 shape:

- `decrementTM_run_succ_ofCfg`, at exact time `2q + 2` where
  `q = (w.takeWhile (· = false)).length`;
- `decrementTM_run_underflow_ofCfg`, at `2|w| + 2`.

The **proof route must not copy the increment proof.** `decrementTM` is
`incrementTM` conjugated by bit complement, so its contracts are derived from
increment's proved framed contracts by a public symbol-complement transport
lemma (decision 12.7.4).

**C2 — `counterLoopTM`, the counter-driven loop host.** Given a body
`B : MultiTapeTM k Bool S` with a re-entry anchor `a`, the host has
`k + 1` tapes, the last one the counter, and states `S ⊕ FlagPhase`.

- At the anchor it runs `decrementTM` on the counter.
- On success it re-enters the body at `a`.
- On underflow it exits to a live `done` anchor.
- If a body round reaches a designated body exit (for a simulator: the
  simulated machine halted), the host exits to a second live `escape`
  anchor.

Its contract `counterLoopTM_run` is stated over **arbitrary configurations**
and has three parts:

- **The body's hypotheses.** A body invariant `P`. A round contract: from any
  `c` with `P c` at `a`, the body reaches, at the exact time `τ c > 0`, either
  the anchor again (with `P`, giving `next c`) or the exit (giving
  `exitCfg c`), without revisiting `a` earlier. And the body never touches the counter
  tape, which the host's embedding enforces.
- **The conclusion.** From the host configuration carrying `c` and a counter
  word `w` of value `d`, delimited:
  - if no round exits early, the host reaches `done` after exactly `d`
    rounds, with body part `next^[d] c` and counter `List.replicate |w| true`;
  - otherwise it reaches `escape` at the first exiting round `r < d`.
- **Total time, exact:** `Σ_{r<d} τ(next^[r] c)` plus the decrement costs
  `Σ_{v=1}^{d} (2ν₂(v) + 2) + (2|w| + 2)` (amortized, at most `4d + 2|w| + 2`)
  plus explicit per-round dispatch constants, fixed when the statements are
  drafted, in the first case; correspondingly in the second. **Uniform-bound
  corollary:** if `τ c ≤ B` whenever `P c`, the total is at most
  `d·B + 4d + 2|w| + O(d)`. Both cases come with no earlier exit and with trajectory
  bounds (counter head within `[pos − 1, pos + |w|]`, body heads as the body's
  own).

C2 is assembled from the §12 layer: the embedding for the body's tape
selection, seams for the anchor/decrement alternation, and the C1 contracts.
No loop-host proof is copied.

**Decisions (user, 2026-10-10).**

1. **Counter placement: a dedicated extra tape**, the host's last tape.
2. **Exits: two live anchors**, `done` and `escape`. A consumer attaches one
   continuation to each with two `seamCompTM` applications, so no new
   composition lemma is needed. A corollary drops the `escape` hypothesis for
   bodies that never exit early. The outermost machine adds its halt once.
3. **Round cost: an exact per-round cost function `τ` of the body
   configuration at the round's start.** The total time is stated exactly as
   the sum over the run's rounds. A round-indexed cost is the special case
   `σ r := τ(next^[r] c)`. A consumer that knows only a bound takes `τ` to be
   the first-return time, which is unique since the contract excludes earlier
   returns. The **uniform bound `B`** is a corollary. This is the
   sensitivity downstream consumers need, for example simulations whose step
   cost grows with tape content.
4. **Decrement proof route: a symbol-complement transport lemma** (option a).
   The §12.6 fill has landed, so increment's framed traces stay as they are.
   The lemma is generic over machines conjugated by a symbol involution, and
   it lives with C1.
5. **Home: a new `Build/CounterLoop.lean`**, importing Catalog, Embed and
   Seam. The 12.2c per-theme reorganization of `Build/` regroups it later.
6. **Scope: the amortized total is stated over the whole run**, not only
   per round.

**Statement phase (2026-10-10).** `Build/CounterLoop.lean` landed with 13
definitions and 10 sorried theorems. The refinements made while drafting:

- **The exit is an `Option S`.** The no-escape corollary is the
  instantiation `exit = none`, so no separate statement is needed.
- **The round hypotheses are stated along the orbit**, not through an
  invariant `P`. This is weaker and so more general; a consumer with an
  invariant derives them.
- **The uniform-bound corollary is pure arithmetic** over the exact time
  (`counterLoop_time_le`). Two amortization lemmas are stated: one for
  prefixes (`4r + 2|w|`) and one for the whole run (`4d + 2|w| + 2`).
- **`decrementTM` is defined as the conjugate** of `incrementTM` by
  `Equiv.boolNot`, through a generic `MultiTapeTM.mapWorkSymbols`. The C1
  contracts are therefore transports of the §12.6 ones.
- **The host has no dispatch steps.** Transitions into the anchor and the
  exit are redirected in place, so the time is exactly the round times plus
  `counterOverhead`.
- **Imports.** Seam is not imported, since consumers compose through
  `seamCompTM_run_ofCfg`. As with `Build/Zone.lean`, the file stays out of
  the `TuringMachine` facade during the statement phase.
- **The counter value** is Mathlib's `Nat.ofDigits 2 (w.map Bool.toNat)`,
  written inline; no new value function is defined.

The executed pre-ship check is `campaign/gates/s12-counter/evidence/`, and the gate
pack is `campaign/gates/s12-counter/{pack,bundle}.md`.

**Statement gate CLOSED (round 1, 2026-10-10: 0 blockers, 0 majors, 1 minor,
5 notes; `campaign/gates/s12-counter/findings.md`).** No false theorem and no missing
soundness hypothesis. Three notes correct or extend this design:

- **SC-4: two continuations need a public prefix lemma.** Two `seamCompTM`
  applications do wire both exits. The escape path through the first
  composite, however, needs the pre-dispatch prefix correspondence, which
  `seamCompTM_run_ofCfg`'s `hexit` cannot provide. The existing private
  `seamComp_left` (`Build/Seam.lean`) proves exactly that. It is to be
  promoted when the first two-continuation consumer is assembled, not copied.
  This corrects decision 12.7.2's claim that "no new composition lemma is
  needed."
- **SC-3: the NTIME consumer needs a nondeterministic lifting.** The host's
  contracts are deterministic (`MultiTapeTM`, `runFrom`). Before the NTIME
  hierarchy fill, a choice-stream lifting contract is needed, with branch
  alignment through the bookkeeping pauses. **Closed (user, 2026-10-13):** C1 takes the
  guess-first route (C1 design note §6, decision 1): the choice word is written first and then
  interpreted deterministically, so no nondeterministic loop host is needed.
  The shared pieces landed with C1 (PR #87, 2026-10-14): the slice lemma in
  `Nondeterministic.lean` (Part A) and the nondeterministic phase host in `Build/NDHost`.
- **SC-5: an optional visited-set corollary.** A public `spaceUsedByTape` or
  visited-set corollary of the trajectory clauses would save the space
  consumers repeated bookkeeping.

Next: the fill batch, after RB5 merges so the host proof can cite the
promoted `MultiTapeTM.runFrom_mapState_of_agreeOn`. ZF-B3's continuation
follows that fill. The existing private
clocks are on the 12.2c tasklist as re-derivation targets (plan §4d,
item 12).


### 12.8 Configuration-graph rows (design draft, 2026-10-10; for the statement phase)

*Drafted from the S1 research (maintainer-commissioned), recorded for the user's decisions 12.8.1–12.8.6. The maintainer's alternative for 12.8.1 is at the end.*

**Why.** The user chose design A for S1b, the summit of `ConfigGraph.lean`:
a configuration-level simulator built on §12 rows (decision log, 2026-10-10).
The S1 research found six capabilities that no public row provides.

| Gap | Missing capability |
|---|---|
| GAP-1 | a native-input-dependent clean seam |
| GAP-3 | a framed compare |
| GAP-4 | a configuration codec with transition application |
| GAP-5 | writing a word at a displaced head |
| GAP-6 | seek over delimited records |
| GAP-7 | two continuations after `counterLoopTM` |

This note proposes reusable rows for all six. Their consumers are every
configuration-graph walker of the campaign:

- S1b (`NSPACE ⊆ DTIME(2^{O(S)})`, hence `NL ⊆ P`);
- Savitch;
- the `PATH` reduction;
- the space hierarchy;
- `TQBF ∈ PSPACE`;
- `NP ⊆ PSPACE`.

**Constraints.**

- (i) **G1** is generalizing `Build/Embed`, `Build/Seam`, Catalog's R3
  sweeps and `FinTM.bufferTape` to `{Symbol : Type*}` in place. A row that
  extends those files' private traces waits for the G1 gate.
- (ii) **G2** (`copyMapTM`/`transferMapTM`) owns the mapped-sweep scanner in
  Catalog. Rows of that family are coordinated with it: one trace per routine
  family.
- (iii) Every row has a framed contract in the §12.6/§12.7 shape (template
  below).
- (iv) The campaign deciders are `FinTM Bool`. `incrementTM`, `decrementTM`,
  `counterLoopTM`, the compare contracts and the Loop hosts stay at `Bool` after
  G1. The record layer is therefore **binary**: decision 12.8.1.

#### Contract template (all rows)

For a tape `i` and a word `w`, write **`Delim d i w`** for the §12.6
hypothesis `∀ p, -1 ≤ p → p ≤ |w| → d.workTapes i (d.workTapePos i + p) =
bufferTape w p`. That is, `w` sits at the head with blanks at `-1` and `|w|`.
Each row `R` states, from any `d` in its start phase:

1. **Exact time** `τ`: `R.runFrom d τ = finish`, where `finish` is `d` with only
   the listed cells and control changed. Every other cell, every head, the
   native input position and the output are unchanged unless the row says
   otherwise.
2. **No earlier exit:** `∀ t < τ, state ≠ done`. (For verdict anchors, this is
   `∀ b`.)
3. **Trajectory:** touched heads stay in a stated interval, typically
   `[pos − 1, pos + |w|]`, and the other heads are fixed. Space follows by
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. That lemma now lives in
   `Build/Catalog.lean` (moved from `Build/Zone.lean` by the B4 pre-issue promotion,
   2026-10-12), so Catalog rows and their consumers can cite it.

The time constants below are indicative. The statement phase fixes them by
the executed pre-ship check, as in §12.6 practice.

Where an exact closed form is unnatural (R8.7's step row), the contract is the
first-return form instead: `∃ t ≤ B`, plus the no-earlier-exit clause.
`counterLoopTM` consumes it with `τ :=` that `t`, which is unique (decision
12.7.3).

#### R8.1 Framed compare (GAP-3)

- `compareTM_run_ofCfg (fst snd) (hne : fst ≠ snd) (u v) (d)
  (hstate : d.state = some .run) (hu : Delim d fst u) (hv : Delim d snd v)`.
  - Exact time `2·δ + 2`, with `δ` the first index where `u` and `v` differ or
    either word ends (`δ ≤ min |u| |v|`, the private `catalog_compare_stop`).
  - Finish: `d` with state `done (decide (u = v))`, every tape unchanged.
  - No earlier `done b`. Trajectory: both heads in `[pos−1, pos+δ]`.
- **Alphabet:** generic with `[DecidableEq Symbol]`. G1 makes `compareTM`'s
  definition generic and keeps its contracts at `Bool`, so the framed row is
  stated generically from the start, and the canonical `compareTM_run` is
  re-derived from it by a sanctioned body swap, exactly as §12.6 did for
  copy/transfer/clear.
- **Trace:** generalize `catalog_compare_trace`, `catalogCompareF` and
  `catalogCompareR` over an outer frame and two start coordinates, on the
  shared `catalog_trace_run` skeleton. No second trace.
- **Home:** `Build/Catalog.lean`, **after the G1 gate**.
- **Note:** a record is a list of blank-separated fields (R8.7), so
  `recordEqTM` is `F` framed compares with R8.3 seeks between them.

#### R8.2 Fold: a finite-state scan with a verdict (new family member)

- `foldTM (i) (δ : A → Symbol → A) (a₀ : A) [Fintype A] [DecidableEq A]`.
  Phases are the forward pass `scan a`, the return `rewind a`, and the anchor
  `done a`.
- `foldTM_run_ofCfg (hw : Delim d i w)`:
  - exact time `2|w| + 2`;
  - finish: `d` with state `done (w.foldl δ a₀)`, all tapes unchanged;
  - no earlier `done`; trajectory `[pos−1, pos+|w|]`.
- **Why a row:** every read of a record field into finite control is a fold.
  That covers the state field, the tag field, "find the marked cell and its
  content and whether it sits at a field end", record validity, and
  acceptance tests. Validators elsewhere (TQBF's well-formedness pass, the
  `PATH` shape checks) are folds too.
- **Alphabet:** generic. **Trace:** `catalog_trace_run` with a read-only
  forward family, as for `copyTM` without the destination. **Home:** Catalog,
  after G1.

#### R8.3 Seek over delimited words and records (GAP-6)

- `skipTM i`: from `Delim d i w`, move right to the word's right delimiter
  and one cell beyond, the next word's first cell. Exact time `|w| + 1`; no
  write; trajectory `[pos, pos+|w|+1]`. `skipBackTM i` is the mirror, starting
  on the cell after the left delimiter of the previous word.
- `skipTM_run_ofCfg` and `skipBackTM_run_ofCfg` have the template shape, with
  the finish `{d with workTapePos i := pos + |w| + 1}`.
- `seekFieldsTM i m` (`m` fixed) composes `m` skips by `seamCompTM_run_ofCfg`.
  `seekEndTM i` skips until the next word is empty (two consecutive blanks);
  it is a fold-guarded loop, under the same skeleton.
- **Consumers:** record navigation (R8.7, S1b's table, Savitch's frame stack),
  and **G4**, which "scans outward across zones, using the separators". Both
  skip blank-separated words, so G4 should cite `skipTM` rather than trace its
  own scan.
- **Trace:** this is the forward half of the R3 trace. Add a forward-only
  sibling of `catalog_trace_run` (`catalog_forward_run`, private), to be shared
  with R8.2's forward phase.
- **Alphabet:** generic. **Home:** Catalog, after G1, **coordinated with G2/G4**.

#### R8.4 Writing words at displaced heads (GAP-5)

- **Computed words** are G2's `copyMapTM`/`transferMapTM` (`merge` and
  `extract`). With `extract := fun _ => b` they fill a blank-free interval with
  a constant (`fillTM i b` is the in-place case `src = dst`, which G2 must
  admit or state separately). Nothing new: G2.
- **Fixed words**: `writeConstTM i (w₀ : List Symbol)` writes the hardwired
  `w₀` from the head and returns.
  - `writeConstTM_run_ofCfg`: exact time `2|w₀| + 1`; finish: cells
    `[pos, pos+|w₀|)` hold `w₀` (old contents arbitrary), head back at `pos`;
    trajectory `[pos, pos+|w₀|]`.
  - The machine is a straight-line chain; its proof uses the public
    `FinTM.emit_run` pattern adapted to writes, so it shares no Catalog trace.
  - **Home:** new `Build/Scan.lean`; **can land now**.
  - **Consumers:** record field initializers (state code, tag code), marker
    cells, per-round patterns inside R8.6's body.

#### R8.5 Native-input rows (GAP-1)

All three are generic over `Symbol`, cite the public `FinTM.rewind_scan` and
`timed_rewind`, and live in new `Build/Scan.lean` (**now**). EmitIterBody's
private startup (`body_start`, `copy_step`, `rwTape_*`, `rwInput_*`) is the
same routine and should be re-derived from `inputCopyTM` in 12.2c T2 (CH7-D2,
coordinated with Aparna).

- `inputCopyTM i`: copy the native input onto tape `i` from the head, then
  rewind both heads.
  - Start: input head at `1`, `Delim`-free destination (old contents
    arbitrary).
  - Exact time `2|x| + c`. Finish: `[pos, pos+|x|)` holds `x`, input head at
    `1`, tape head at `pos`.
  - Trajectory: input head in `[0, |x|+1]`, tape head in `[pos−1, pos+|x|]`.
- `inputLengthTM i`: count `|x|` into a fixed-width binary counter on tape `i`
  (one `incrementTM` per input symbol, cited at its framed carry-sensitive cost).
  - Exact time `Σ_v (2·ν₂(v) + 2) + |x| + c`, amortized at most `4|x| + c`
    (§12.7's potential).
  - Finish: the counter holds `bits |x|` padded to its width, and the input head
    is back at `1`.
  - Bool only, because it uses `incrementTM`. Its home is `Build/CounterLoop.lean`
    or `Scan` importing it.
- `inputSeekTM i c`: move the input head to the binary position `p` held at
  tape `i`.
  - Mechanism: copy `p` to the counter tape `c` (`copyTM_run_ofCfg`), rewind the
    input (`timed_rewind`), then `counterLoopTM` with the one-step body "input
    right".
  - Exact time: the copy (`2|p| + 2`), the rewind (`≤ pos + 2`), then
    `p + counterOverhead w (p + 1)`.
  - Finish: input position `p`, counter tape all-`true` (`counterLoopTM_run_done`).
    Callers clear it (`clearTM_run_ofCfg`).
  - Bool only.
  - **Consumers:** R8.7's input read, `PATH_mem_NL`'s matrix indexing (`u·n + v`),
    virtual-input callers needing random access.
- Packaged combinator **`exists_inputCallTM`** = `inputCopyTM` +
  `exists_installCallTM`: call a function-level machine on the native input at a
  clean seam. It is GAP-1's general form. **Home:** new `Build/InputCall.lean`,
  importing Loop, **now**. It touches no G1 file, but must not collide with
  12.2c T1 item 11's Loop edits.

#### R8.6 Counter-driven expansion

- `expandTM (pat : List Bool)` = `counterLoopTM` around `writeConstTM pat`
  followed by a `skipTM`-like advance. From a counter word of value `d` at the
  counter tape and a blank region on tape `i`, it writes `pat` `d` times
  contiguously.
  - Exact time `Σ_{r<d} τ_pat + counterOverhead w (d+1)`, by
    `counterLoopTM_run_done` and `counterLoop_time_le`.
  - The written word is `pat`ⁿ with `n = d`, which is a framed `Delim` for later
    rows.
- **Consumers:**
  - S1b and Savitch: blank tape fields of `2s+1` cell codes, with `s` given in
    binary by the constructor;
  - `spaceConstructible_logSpace`/`_linear`/`_poly` (binary ↔ unary);
  - the space hierarchy's window radius and clock width (the window route, §16b item 3; the
    budget loop is gone);
  - the §12.7 clocks.
- Bool. **Home:** `Build/CounterLoop.lean` (not G1-owned). **Can land now**,
  once R8.4's `writeConstTM` exists.

#### R8.7 Configuration records (GAP-4)

**Pure layer** (new `Build/CfgRecord.lean`; statements now).

- **Parameters:** a source `M : MultiTapeTM k Bool Q`, `[Fintype Q]`, a window
  radius `s`, an input length `n`, and a finite **tag** type `T` with an update
  `upd : T → Option Bool → T`. The tag carries emission history; the
  configuration graph instantiates `T := OutSummary` and `upd` := the Q1 append
  table. A Build-level row cannot mention `OutSummary`, which is defined
  downstream in `ConfigGraph.lean`; hence the parameter.
- **`cfgRecord n s (c : Cfg k Bool Q x) (τ : T) : List (List Bool)`**, a list of
  `k + 3` **blank-separated fields**, each a blank-free Bool word:
  - **F0** state: a one-hot code of `c.state : Option Q`, width `|Q|+1`;
  - **F1** input position: `c.inputPos` in little-endian binary at the fixed
    width `|bits (n+1)|`;
  - **F2…F(k+1)** tape `i`: `2s+1` three-bit cells
    `(nonblank, value, head-here)` for `z = −s … s`;
  - **F(k+2)** tag: a one-hot code of `τ`.

  Field lengths depend only on `(n, s)`, so records compare field-wise and
  enumerate by counting.
- **`recordTape`** lays the fields out with one blank between fields (and
  between records); the G3 carrier's separator discipline.
- **Window predicate.** `Turing.Cfg.InWindow s` already exists, defined in
  `ClassPSPACE/TQBF.lean`, *downstream* of every Build file. **Decision
  12.8.2:** relocate it verbatim (same name and body) to `CfgRecord.lean` and
  delete TQBF's copy. That is a surface move in a C1d-owned file, so it waits
  for C1d. The alternative is a second predicate under another name, a
  definitional duplicate.
- **`cfgRecord_inj`:** for `InWindow s c` and `InWindow s d` on the same input,
  `cfgRecord n s c τ = cfgRecord n s d τ' ↔ core c = core d ∧ τ = τ'`. It
  follows `ConfigCount.coreCode_inj`.
- **`cfgRecord_valid`:** a word list is a record iff a fold (R8.2) accepts each
  field. One-hot fields, three-bit cells with exactly one head mark per tape
  field, and `F1 ≤ n+1` (the last by `compareTM` against `bits (n+1)` or by
  a fold).

**Rows** (`Build/CfgRecord.lean`). The statements can be drafted now. The
fills need R8.1–R8.3, so they come after the G1 gate.

| Row | Effect (framed; record at the head of tape `r`; scratch tapes blank) | Built from |
|---|---|---|
| `recordReadTM` | Verdict `done (q, ι, σ, τ, edge)`: state, the input symbol at the coded position, the `k` scanned symbols, the tag, and which tape heads sit at a field end. Record unchanged; input head restored | R8.2 folds per field, R8.3 seeks, R8.5 `inputSeekTM` on a copy of F1, `clearTM` |
| `recordApplyTM a` (`a : Action k Bool Q` fixed, `upd` fixed) | Rewrites the record of `c` into that of `a.apply c`, with the tag updated by `a.output`. Per tape it rewrites the marked cell and moves the mark; F1 gets `incrementTM`/`decrementTM` (framed), with the clamp read off the edge data; F0 and the tag go through `writeConstTM`. Precondition: no mark leaves its field (checked by the read) | R8.4, R8.3, Catalog `incrementTM_run_*_ofCfg`, CounterLoop `decrementTM_run_*_ofCfg`, and one local `markShiftTM` per tape field (new, record-specific) |
| **`recordStepTM M upd`** | **The GAP-4 row.** Verdict `done true` with the record of `M.step c` (tag updated) if that configuration is in the window. Verdict `done false` with the record unchanged otherwise, or if `c` is halted (`done true`, unchanged: a halted vertex is its own successor). First-return contract, `t ≤ C_M·(L + n + 1)` with `L` the record length; trajectory inside the record interval and `[0, n+1]` on input | `recordReadTM` ; finite dispatch on `M.tr` ; `recordApplyTM a`, glued by `seamCompTM_run_ofCfg` and two-continuation dispatch (R8.8). An NDTM is consumed per choice bit through `NDTM.fixChoice` (S1a's promotion) |
| `recordInitTM` | Writes the record of `M.initCfg x` with tag `τ₀`, from a radius word (binary `s`) and the input length counter | R8.4, R8.5 `inputLengthTM`, R8.6 `expandTM` |
| `recordEqTM` | Verdict: the two records at the heads of tapes `r`, `r'` are equal | `k + 3` R8.1 compares with R8.3 seeks |
| `recordTestTM P` (`P` a finite predicate on `(state, tag)`) | Verdict `P (c.state, τ)`. Acceptance is `P := (· = none) ∧ (· = accept)` | R8.2 on F0 and the tag field |
| `recordNextTM` | Lexicographic successor among *valid* records (odometer over all field bits, skipping invalid ones), or an overflow verdict | `incrementTM` per field, carry cascade, `recordValidTM` |
| `recordValidTM` | Verdict `cfgRecord_valid` | R8.2 |

**Space.** Every record row is framed inside its record interval plus
`O(L)` scratch. `L = O(k·s + log n + |Q|)`, which is `O(S n)` for Savitch at
`S ≥ logSpace`. This is why F1 is **binary**: a one-hot input track would make
`L = Θ(n)` and break `SPACE(S²)` at `S = log`.

#### R8.8 Two continuations after a two-exit host (GAP-7)

- Promote the existing private `Turing.seamComp_left` (`Build/Seam.lean:173`)
  as **`seamCompTM_runFrom_left`**, statement unchanged. This is SC-4's
  resolution: "expose the existing prefix lemma … do not copy its induction".
- Add one corollary, **`seamCompTM₂_run_ofCfg`**: for a host with two live
  anchors `e₁`, `e₂` (`counterLoopTM`'s `done` and `escape`), nesting two
  `seamCompTM`s attaches a continuation to each. It states the run along
  whichever exit is reached, with the other continuation's summand
  unreachable.
- Generic after G1. **Home:** `Build/Seam.lean`, **after the G1 gate**.
- **Consumers:** every `counterLoopTM` user with an early exit. S1b's BFS
  (queue empty / counter exhausted), the space hierarchy's windowed runner (halt, window
  exit, clock; the window route, §16b item 3), and `recordStepTM`'s internal dispatch.

#### Placement and timing

| Row(s) | Home | Touches a G1-owned file? | When |
|---|---|---|---|
| R8.4 `writeConstTM`; R8.5 `inputCopyTM`, `inputSeekTM`, `inputLengthTM` | new `Build/Scan.lean` (imports CounterLoop) | no | **now** |
| R8.5 `exists_inputCallTM` | new `Build/InputCall.lean` (imports Loop, Scan) | no | **now** (coordinate with 12.2c item 11) |
| R8.6 `expandTM` | `Build/CounterLoop.lean` | no | **now**, after `writeConstTM` |
| R8.7 pure layer, `InWindow` relocation | new `Build/CfgRecord.lean`; `ClassPSPACE/TQBF.lean` | no; TQBF is C1d's | statements now; relocation after C1d |
| R8.1 framed compare; R8.2 fold; R8.3 seek | `Build/Catalog.lean` | **yes** | **after the G1 gate**, with G2 (shared scanner) |
| R8.4 fill (in-place mapped sweep) | Catalog (G2) | **yes** | with G2 |
| R8.8 seam promotion + corollary | `Build/Seam.lean` | **yes** | **after the G1 gate** |
| R8.7 record rows (fill) | `Build/CfgRecord.lean` | no, but cites R8.1–R8.3 | fill after R8.1–R8.3 land |

The process is the house one: maintainer-drafted statements; an executed
pre-ship check (concrete configurations, displaced heads, nonblank outer
frames, `w = []`, `s = 0`, `k = 0`, a halted source); a short statement gate;
fill batches split now/after-G1; a fill gate.

#### Consumers: which rows each walker uses

| Consumer (audited sketch) | Rows |
|---|---|
| **S1b** *(historical: S1b stopped, fills-6; the target is proved at ARM level, §14 H12, 2026-10-14)* `NSPACE_subset_exp_dtime` (BFS; then `NL_subset_P` and Ex 4.3 by the binding route) | R8.7 `recordInitTM`, `recordStepTM` (×2 choice bits), `recordEqTM`, `recordTestTM`; R8.3 table navigation; R8.4/G2 append and counter initialization; R8.6 window fields; R8.8; existing `counterLoopTM`, `embedSilentRetTM_run` (constructor capture), `seamCompTM_run_ofCfg`, `copyTM_run_ofCfg` |
| **Savitch** `savitch` ("frame stack … catalog copy/compare/increment … one extra bank runs the vertex-adjacency test") | `recordStepTM` + `recordEqTM` for `adj(u, v)` (`u = v ∨ step u = v`, both choice bits); `recordNextTM` + `recordValidTM` for the midpoint enumerator; R8.3 seek over the frame stack; `copyTM`/`clearTM` for frame push/pop at **fixed intervals** (note 7); `incrementTM` for the depth field; R8.8 for the recursion's two returns. Space contracts of every row are load-bearing |
| `spaceConstructible_poly`/`_logSpace`/`_linear` | R8.5 `inputLengthTM`; R8.6 `expandTM`; `incrementTM` |
| **`PATH_NLComplete`** hardness (adjacency "by one local transition-table check", logspace) | The sketch's engine is the ARM layer (`arm_decides`). Optionally, a TM route: `recordStepTM`'s space clause with binary F1 gives `O(log n)`-space adjacency deciders for the index languages. Decision 12.8.4 |
| **`PATH_mem_NL`** (matrix indexing) | R8.5 `inputSeekTM` (once a nondeterministic host exists, SC-3; superseded 2026-10-13: C2 is written as programs, §16b item 4) |
| **Space hierarchy** `space_universal`, `space_hierarchy`. **Superseded 2026-10-12 by the window route** (§16b item 3): `space_universal` is forward-only (no interval counters, clock or probe/replay), and `space_hierarchy` runs a self-application universal `U₀` in a window on the record rows | **Now:** R8.7 (`recordInitTM`, `recordStepTM`, `recordTestTM`) under a configuration-count clock (`counterLoopTMVia`), with H2 (step block), H3 (windowed runner, three exits) and H5 (native and binary-position input devices; corrected 2026-10-13: native and the bounded-prefix ruler device, user decisions B1–B2). The earlier route (interval counters, budget loop, R8.8 success/cap exits) is dropped |
| **`TQBF_mem_PSPACE`** (validate-first, depth-first assignment walker, per-clause CNF evaluation) | R8.2 folds (validation, clause evaluation), R8.5 `inputSeekTM` (re-reading prefix bits and matrix bytes), `incrementTM` / a trit odometer (`recordNextTM`'s carry discipline) for the walker, R8.3 seek on the assignment word |
| `NP_subset_PSPACE` | existing `incrementTM` (certificate enumerator) and `vhostEmitTM` (virtual input); R8.8 for accept/exhaust |

#### S1b's machine plan as a composition of these rows

*Historical (2026-10-14): S1b stopped (fills-6), and its target is proved at ARM level (§14 H12).
The rows this plan uses keep one remaining consumer, B6's window route (rows 17–18).*

**Host.** A `FinTM Bool`. It has the native input; the constructor's embedded
tapes plus a capture tape; tape `Tab` (the record table); `Cur₀` and `Cur₁`
(successor workspaces); `Rad` (radius and length words); scratch for
`recordStepTM`; and `Cnt`, the counter, which is the last tape, as
`counterLoopTM` requires.

1. **Radius.** Run `M_S` (from `hS`) under `embedSilentRetTM_run`, with its
   output `bits (S n)` captured, then rewind the input (`timed_rewind`). Its time
   is at most `M_S.configBound n (a·S n)` (`ComputesInTime.of_spaceUsed_le`).
   Multiplying by `c₀` is a fixed binary shift-and-add or `c₀` copies.
2. **Initial table.** Lay down `recordInitTM` (via `inputLengthTM` and
   `expandTM`) on `Tab`, with tag `empty` and a one-bit flag field `[false]`
   ("unprocessed") appended to each record.
3. **Counter.** Copy `Tab`'s first record's fields to `Cnt` contiguously
   (`copyTM_run_ofCfg` + `skipTM`), then fill it with `true` (G2 in-place map).
   Its value `2^{bits(record)} − 1` exceeds the record count `V`, so `done` is
   unreachable before `escape` (or is wired anyway by R8.8).
4. **Round** (the `counterLoopTM` body, anchor `a`). `seekFieldsTM` finds the first
   record whose flag is `false`; if there is none, it reaches the body's exit, and
   the host escapes. Otherwise:
   - copy that record to `Cur₀` and `Cur₁`;
   - run `recordStepTM (N.fixChoice false)` on `Cur₀` and
     `recordStepTM (N.fixChoice true)` on `Cur₁`;
   - for each successor in the window, scan `Tab` with `recordEqTM`, and if it
     is absent, append it at `seekEndTM` with flag `[false]`;
   - set the processed record's flag (`incrementTM` on the one-bit field);
   - clear the workspaces, rewind `Tab` (`skipBackTM` to the table start), and
     return to `a`.

   The round's first-return time `τ` is at most `C·(|Tab| + n + L)` with
   `|Tab| ≤ V·(L + F)`.
5. **Verdict.** From either exit (R8.8), fold `recordTestTM accept` over
   `Tab`'s records and emit `[true]` or `[false]`; then halt (a fixed emission
   tail; `FinTM.emit_run` pattern).
6. **Correctness:**
   - The table is the windowed-reachable set: the BFS invariant, with each record
     identified with a `coreSum` by `cfgRecord_inj` at `T := OutSummary`.
   - Membership follows by S1a's targets 1–4 and the audit's note-6 bridge
     (canonical decoding, outside-window rejection by `recordStepTM`'s false
     verdict, path lifting from the true initial configuration, all accepting
     vertices tested, the initial vertex in the table).
7. **Time:**
   - `counterLoop_time_le`: `V·B + 4V + 2|w| + 2` with `B = O(V·L + n)`. Add the
     constructor and startup.
   - Everything is at most `K·2^{c'(S n+1)}`, by the generalized `configBound`
     arithmetic and `n + 2 ≤ 2^{S n + 1}`.
   - All budgets are evaluated at `n` itself. **No monotonicity of `S` is used.**

#### Decisions for the user (12.8.x)

1. **Binary records** (recommended). The rows stay on the `Bool` counter stack,
   with no generic increment or `counterLoopTM`. The alternative is a
   rich-alphabet record: one cell per simulated cell, a simpler step machine, and
   `alphabet_reduction{,_spaceUsed}` at the end. It needs `incrementTM`,
   `decrementTM` and `counterLoopTM` generalized over two designated digit
   symbols (Catalog is G1-owned; CounterLoop is not).
2. **`Cfg.InWindow` relocation** from TQBF to `Build/CfgRecord.lean`, after C1d.
3. **`recordStepTM`'s contract form:** first-return with a bound (recommended),
   or an exact closed form.
4. **`PATH` hardness engine:** ARM (as sketched) or TM record rows with space
   clauses.
5. **Fold and seek in Catalog** (one trace family, after G1), or in `Scan` now
   with their own private skeleton. The latter is faster, but it is a second
   trace of the R3 forward pass.
6. **EmitIterBody dedup** onto `inputCopyTM` in 12.2c T2 (coordinate with
   Aparna).

#### Decisions 12.8.1–12.8.6 (2026-10-10)

1. **Rich-alphabet records** (user): multi-track record cells, mark moves as
   G2 mapped sweeps, and Bool counter rows on rich tapes through **one new
   embedding transport**. Finished by `alphabet_reduction` and
   `alphabet_reduction_spaceUsed`. The maintainer's alternative below is
   adopted, and the binary plan above is superseded where they differ.
2. **`Cfg.InWindow` moves** verbatim to `Build/CfgRecord.lean` after C1d
   (default).
3. **`recordStepTM` has a first-return contract with a bound** (default).
4. **`PATH`-hardness stays on the ARM engine**, as audited (default). The
   record-row route remains an option.
5. **Fold and seek live in Catalog, after the G1 gate** (user), sharing the
   R3/G2 trace, one trace per routine family.
6. **EmitIterBody's private input-copy startup is re-derived** from the new
   input rows in 12.2c T2, with the ch7 owner (default).

**Next.** A revised statement draft for the rich design. What can start
now: the embedding transport and the alphabet-generic input and
constant-write rows. The record rows, fold and seek wait for G1 and G2.

#### Maintainer's alternative for 12.8.1: rich-alphabet records through one embedding transport

Records could follow the §13d pattern instead of being bit-coded. Each record
cell is one rich symbol with tracks (content `Option Bool`, head mark, field
separators), as in the G3 `ZoneCell` carrier. Moving a head mark is then a G2
mapped sweep on one track, and no per-tape `markShiftTM` is needed. Fields
compare through the generic framed compare, and folds read one symbol per
cell.

The binary rows (`incrementTM`, `decrementTM`, `counterLoopTM`, the compare
contracts) need not be generalized. **One new transport lemma** runs them on
rich tapes: the embedding analogue of §12.7's `mapWorkSymbols`, which lifts a
`Bool` machine along `e : Bool ↪ Γ`. Its contract holds from configurations
whose work cells all lie in the image of `e` or are blank, which a dedicated
counter tape satisfies.

The simulator is finished by `alphabet_reduction` for time and by
`alphabet_reduction_spaceUsed` for space (space at most `(N+1)·space + k`).
The latter keeps Savitch and the space hierarchy within their bounds. The
input-position field stays binary over designated digits, so record length
stays `O(k·s + log n + |Q|)`.

The cost is the transport lemma, and records that wait for G2's mapped sweeps
(after the G1 gate). The gain is that the record machines become compositions
of generic rows instead of bit-group machines, and §12.8 and §13d share one
multi-track discipline.


### 12.8a Statement draft for the rich-alphabet design (2026-10-10)

*Recorded from the S1 agent's draft. Its probe is `campaign/items/s12-8/S128StatementsProbe.lean.txt`; run by the maintainer against the G1 side-branch tree it gives 0 errors and 12 sorry warnings, one per statement left to the fill. Maintainer decisions O1, O4, O5, O6 and the user's O2, O3, O7 are recorded at the end (§8).*

*Landed as statements on 2026-10-11, branch `integrate/s12-8-statements`: §8 lists the landed names, which supersede the draft's below where they differ, the changes from the draft, the R8.0b target signatures, and the open questions for the statement gate.*

*Draft for the statement phase, 2026-10-10. Base: campaign `19964447`; G1 side branch `s13d/g1`
(`10c2c08d`, PR #15, awaiting its gate).*

**Probe.** `drafts/s12-8-probe.lean`, with its output in `s12-8-probe.out`. It contains the
exact Lean of everything below.

- Against the G1 tree (`tools/leanprobe-g1.sh`): **0 errors, 0 warnings other than 12
  `declaration uses 'sorry'`**, one per proposed statement whose proof is fill work.
- Part A, the transport, is fully proved and also elaborates at the campaign HEAD
  (`tools/leanprobe.sh`, extracted as `s1work/p8/partA-head.lean`): 0 errors, 0 warnings.
- Every exact time below that the probe could execute was checked by `decide` on concrete
  configurations (§12.6 practice). That covers seek, the constant writer, the scan with a
  mark-shift instance, the input copier, and the framed compare at displaced heads.

#### 0. What the rich design needs, and the one gap in the decision as worded

Decision 12.8.1 adopts rich record cells, with the `Bool` counter rows run on rich tapes
through one embedding transport. The transport (R8.0) does what was asked:

- it lifts **any** `Bool` machine along `e : Bool ↪ Γ`;
- the lifted increment and decrement rows run on a dedicated digit tape inside a rich host,
  through G1's generic R1 (Part B of the probe).

**It cannot lift a loop with a rich body.** `counterLoopTM M` requires
`M : MultiTapeTM k Bool S`, so lifting it only serves `Bool` bodies. S1b's BFS round, Savitch's
frame step and every record row have rich bodies. After G1, no loop host exists over a
non-`Bool` alphabet. Decision 13d.7 generalized only Seam, Embed, `bufferTape` and the R3
sweeps. It deferred the loop hosts "only when a large-alphabet consumer needs them", and
§12.8's records are that consumer.

The rich design therefore needs **R8.0b, `counterLoopTMVia`**, a counter loop over any
alphabet:

- the body runs through R1 on the first `k` tapes;
- the counter is a dedicated last tape of digits `e b`, decremented by the lifted
  `decrementTM 1 0`, also through R1.

No new trace is needed. The existing round induction is generalized in place, and the
`Bool` contracts are re-derived from the generic ones: at `e = Function.Embedding.refl Bool`
the two tables agree, so Z5's `MultiTapeTM.runFrom_eq_of_agreeOn` transfers. This is the one
substantive addition to the decision; see §5 for its sequencing.

Two smaller findings:

- **The tag type.** `alphabet_reduction` needs `[Fintype Γ]`, and
  `Γ = RecSym N.State T` is `Fintype` only when `T` is. `Turing.OutSummary`, which is frozen,
  derives only `DecidableEq`. So S1b uses `T := Fin 3` through a code of the summary, as S1a's
  private counting already does, or sanctions a `Fintype OutSummary` export. Open decision O4.
- **Space on foreign inputs.** `alphabet_reduction_spaceUsed` hypothesizes
  `∀ x : List Γ, ∀ t, spaceUsed ≤ S |x|`, that is, over **all** rich inputs, including
  non-`Bool` ones. A lifted `Bool` machine reads a foreign symbol as a blank (`decodeBool`), so
  its space on such inputs is not controlled. Every rich space-bounded simulator (Savitch, the
  space hierarchy) must therefore start with a native **input validation fold**, R8.5d, and stop
  on a foreign symbol.

#### 1. R8.0 — the embedding transport

**Home: a new low file `TuringMachine/SymbolLift.lean`, importing `TuringMachine/Finite`.**
The alternative was CounterLoop's `SymbolTransport` section. The transport uses only
`Configuration`/`Deterministic`/`Finite`, and it has consumers below `Build/`: the G3 carrier
(`ZoneSym := Bool ⊕ …` with `e := Sum.inl`) and the Robustness layer. A low home also keeps it
out of `CounterLoop.lean` while that file's §12.7 fill gate is open.

- **Imports:** `Finite` imports `Deterministic`, which imports `Configuration`. Its up-closure
  contains no `Build/` module, so no cycle is possible.
- **Facade:** the `TuringMachine` facade gains one import.
- `mapWorkSymbols` (CounterLoop) can join it at 12.2c's per-theme split.

**Exact declarations** (verbatim in probe Part A, proved):

```lean
def decodeBool [DecidableEq Γ] (e : Bool ↪ Γ) (γ : Γ) : Option Bool :=
  if γ = e true then some true else if γ = e false then some false else none
@[simp] lemma decodeBool_apply [DecidableEq Γ] (e : Bool ↪ Γ) (b : Bool) : decodeBool e (e b) = some b
def Action.liftSymbols (e : Bool ↪ Γ) (a : Action k Bool State) : Action k Γ State   -- writes/emission mapped by e
def Cfg.liftSymbols (e : Bool ↪ Γ) {x : List Bool} (c : Cfg k Bool State x) : Cfg k Γ State (x.map e)
  -- state, heads unchanged; inputPos := Fin.cast _ c.inputPos; cells and output mapped by e
def MultiTapeTM.liftSymbols [DecidableEq Γ] (M : MultiTapeTM k Bool State) (e : Bool ↪ Γ) :
    MultiTapeTM k Γ State   -- reads through decodeBool e, writes through e
theorem MultiTapeTM.liftSymbols_runFrom [DecidableEq Γ] (M) (e) {x} (c : Cfg k Bool State x) (t : ℕ) :
    (M.liftSymbols e).runFrom (c.liftSymbols e) t = (M.runFrom c t).liftSymbols e
lemma MultiTapeTM.liftSymbols_initCfg : (M.liftSymbols e).initCfg (x.map e) = (M.initCfg x).liftSymbols e
lemma MultiTapeTM.liftSymbols_spaceUsed : (M.liftSymbols e).spaceUsed (c.liftSymbols e) t = M.spaceUsed c t
@[simp] lemma Cfg.liftSymbols_state, Cfg.liftSymbols_workTapePos   -- rfl
lemma Cfg.liftSymbols_inputSymbol : (c.liftSymbols e).inputSymbol = c.inputSymbol.map e
def FinTM.liftSymbols {Γ : Type} [DecidableEq Γ] (M : FinTM Bool) (e : Bool ↪ Γ) : FinTM Γ
theorem FinTM.liftSymbols_computesFunInTimeVia (h : M.ComputesFunInTime f T) :
    (M.liftSymbols e).ComputesFunInTimeVia e f T
```

The one-step lemma `MultiTapeTM.liftSymbols_step`, and `moveInputPos_cast`, are `private` in
the real file.

**Proof notes.**

- `MultiTapeTM.runFrom_comm_of_step` (vendored `Deterministic.lean`) is single-alphabet, so the
  run lemma is a direct induction with `runFrom_succ_eq_step`.
- The one-step lemma decodes the input symbol through
  `Cfg.liftSymbols_inputSymbol`, which needs `Fin.cast` care on the boundary tests.
- The work reads decode by `decodeBool_apply`. Writes commute with `Function.update`.
- The output is `(Option.map e o).toList = o.toList.map e`.

**Corollaries after the G1 merge** (probe Part B, proved). These touch no G1 file:

- `FinTM.bufferTape_map (e) (w) (p) : bufferTape (w.map e) p = (bufferTape w p).map e`. It lives
  in `SymbolLift.lean`, which then imports `Simulation`.
- **Framed lifted rows are one-line consequences.** The probe proves the increment success case:
  `((incrementTM k i).liftSymbols e).runFrom (d.liftSymbols e) (2p+2) = (finish).liftSymbols e`.
  So no per-row lifted statement is proposed; consumers rewrite with
  `liftSymbols_runFrom` and cite the `Bool` row.
- **Dedicated digit tape inside a rich host:**
  `(embedEmitTM ι ((incrementTM 1 0).liftSymbols e)).runFrom (embedEmitCfg ι tapes heads pre
  (d.liftSymbols e)) t = embedEmitCfg ι tapes heads pre ((… .runFrom d t).liftSymbols e)`. The
  host's other tapes (rich records) are R1's frame, so the transport's in-range hypothesis is
  only about the dedicated tape. This is the "dedicated counter tape" discipline of decision
  12.8.1, in usable form.

**Finishing.** Two cases:

- **Time.** A rich decider `D : FinTM Γ` with
  `D.ComputesFunInTimeVia e (fun x => [indicator L x]) T` becomes `FinTM Bool` by
  `FinTM.alphabet_reduction e D f T`, which gives `∃ c M', M'.ComputesFunInTime f (c·(T+1))`.
  The constructor and every `Bool` subroutine enter `D` as `FinTM.liftSymbols` /
  `MultiTapeTM.liftSymbols`, with unchanged time (`liftSymbols_computesFunInTimeVia`) and space
  (`liftSymbols_spaceUsed`).
- **Space.** Use `alphabet_reduction_spaceUsed`, subject to the foreign-input caveat of §0.

##### R8.0b — `counterLoopTMVia`, the counter loop over any alphabet

**Home:** `Build/CounterLoop.lean`. **When:** after the G1 gate (it needs generic
`embedEmitTM`/`embedEmitCfg`) **and** after the §12.7 fill gate. The probe's Part E has the
exact text.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1)
def counterLoopTMVia {k} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : (embedEmitTM Fin.castSuccEmb M) redirected by counterLoopRedirect a exit
  -- .dec f  : (embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)) redirected by counterLoopDecExit a
  -- .done / .escape stationary
theorem counterLoopTMVia_run_done   -- counterLoopTM_run_done verbatim with Bool ↦ Γ, plus:
    (hw : ∀ p, -1 ≤ p → p ≤ |w| → ct (cp + p) = bufferTape (w.map e) p)   -- w : List Bool
    -- finish counter cells: `some (e true)`; time `Σ τ + counterOverhead w (d+1)` (unchanged)
theorem counterLoopTMVia_run_escape -- counterLoopTM_run_escape likewise; counter
    -- `bufferTape ((counterWord w (r₀+1)).map e)`
```

- **In-place generalizations (types only, bodies verbatim, G1 rule 2):** `counterLoopCfg` and
  `counterLoopOrbit` become `{Symbol : Type}`. The probe states them as `…Via` copies only to
  avoid a clash.
- `counterLoopTM`, its definition and all `Bool` statements stay byte-identical. Their **proof
  bodies** are swapped to instantiate the generic contracts. The route is
  `runFrom_eq_of_agreeOn` between `counterLoopTM M a exit` and
  `counterLoopTMVia (Function.Embedding.refl Bool) M a exit`. Their dec-phase tables agree
  pointwise (`decodeBool refl γ = some γ`, `Option.map refl = id`, and R1's single-tape action
  equals `decrementTM (k+1) (Fin.last k)`'s), and the other phases agree definitionally.
- **One round induction; net private count down.** `counterLoop_time_le` and the counter
  arithmetic are alphabet-free and reused as they are.

#### 2. The record carrier — `Build/CfgRecord.lean`

**Imports:** `Build/CounterLoop` (for R8.0b) and `TuringMachine/SymbolLift`. **No
`SpaceComplexity` import:** injectivity is stated componentwise rather than through
`ConfigCount.core`, and ConfigGraph converts. **When:** after the G1 merge, since `fieldsTape`
uses generic `bufferTape`. The window predicate lands with the 12.8.2 relocation (after C1d).
The probe's Part F has the exact text.

```lean
inductive RecSym (Q T : Type) where
  | digit (b : Bool)                          -- the `e` of the lift: input, position field, counters
  | cell (content : Option Bool) (mark : Bool)-- one simulated work cell: content track + head-mark track
  | st (q : Option Q)                         -- the state cell
  | tag (τ : T)                               -- the tag cell (emission summary)
deriving DecidableEq
instance recSymFintype (Q T : Type) [Fintype Q] [Fintype T] : Fintype (RecSym Q T) := derive_fintype% _
def RecSym.digitEmb (Q T : Type) : Bool ↪ RecSym Q T
def binDigits (w v : ℕ) : List Bool := (List.range w).map v.testBit       -- little-endian, fixed width
def posWidth (n : ℕ) : ℕ := (Nat.bits (n + 1)).length                      -- 2 ^ posWidth n > n + 1
def cfgRecord {k Q T} {x : List Bool} (s : ℕ) (c : Cfg k Bool Q x) (τ : T) : List (List (RecSym Q T)) :=
  [RecSym.st c.state] ::                                                     -- F0
  ((binDigits (posWidth x.length) c.inputPos.val).map RecSym.digit) ::       -- F1, binary over digits
  (((List.finRange k).map fun i => (List.range (2 * s + 1)).map fun j =>     -- F2 … F(k+1)
      RecSym.cell (c.workTapes i ((j : ℤ) - s)) (decide (c.workTapePos i = (j : ℤ) - s))) ++
  [[RecSym.tag τ]])                                                          -- F(k+2)
def joinFields (fs : List (List Γ)) : List (Option Γ) := List.intercalate [none] (fs.map (List.map some))
def fieldsTape (fs : List (List Γ)) (z : ℤ) : Option Γ := if 0 ≤ z then ((joinFields fs)[z.toNat]?).join else none
def fieldOffset (fs : List (List Γ)) (j : ℕ) : ℕ := ((fs.take j).map (·.length + 1)).sum
theorem fieldsTape_field (fs) (j) (hj : j < fs.length) : ∀ p, -1 ≤ p → p ≤ |fs[j]| →
    fieldsTape fs (fieldOffset fs j + p) = FinTM.bufferTape fs[j] p   -- each field is a framed word
theorem cfgRecord_inj (s) (hc : c.InWindow s) (hd : d.InWindow s) :
    cfgRecord s c τ = cfgRecord s d τ' ↔
      (c.state = d.state ∧ c.inputPos = d.inputPos ∧ c.workTapes = d.workTapes ∧
        c.workTapePos = d.workTapePos) ∧ τ = τ'
theorem cfgRecord_length : (cfgRecord s c τ).length = k + 3   -- proved in the probe
def RecordValid (k n s : ℕ) (Q T) (fs) : Prop :=
  ∃ x (c : Cfg k Bool Q x) τ, x.length = n ∧ c.InWindow s ∧ cfgRecord s c τ = fs
theorem recordValid_iff (n s fs) : RecordValid k n s Q T fs ↔ fs.length = k + 3 ∧ (∃ q, fs[0] = [.st q]) ∧
    (fs[1] is posWidth n digits of value ≤ n + 1) ∧ (each tape field: 2s+1 `.cell`s, exactly one mark) ∧
    (∃ τ, fs[k+2] = [.tag τ])            -- the scan-checkable form, for `recordValidTM`
def RecordAt (d : Cfg K Γ S x) (r : Fin K) (fs) : Prop :=
  ∀ p, -1 ≤ p → p ≤ |joinFields fs| → d.workTapes r (d.workTapePos r + p) = fieldsTape fs p
```

- **Layout discipline.** One blank between fields and between records; no field is empty (F0
  and the tag have one cell, F1 has `posWidth n ≥ 1` cells, each tape field `2s+1` cells). So
  two consecutive blanks mark the end of a table, and every field is a §12.6-delimited word.
  This is the G3 separator discipline, so the generic framed rows apply field by field with no
  save/restore.
- **Space.** A record has `k(2s+1) + posWidth n + 2` cells plus `k + 2` separators, which is
  `O(k·s + log n + 1)`. That is `O(S n)` at `s = c₀·S n` with `S ≥ logSpace`. With
  `alphabet_reduction_spaceUsed`'s `c·(space+1)`, Savitch stays in `SPACE(S²)`.
- **Window predicate.** The probe uses `WindowedP`, a verbatim copy of TQBF's
  `Turing.Cfg.InWindow`. The real file uses `Cfg.InWindow`, relocated here (12.8.2). It **must
  land in the same change** that deletes TQBF's copy: once ConfigGraph imports `CfgRecord` (at
  S1b), TQBF, which is downstream, would otherwise see two definitions.

#### 3. The rows, restated for the rich design

Template (from the §12.8 note), with one change of form:

- **Machines that are single sweeps are defined** and get the §12.6 framed contract: exact
  time, finish configuration, no earlier exit, trajectory.
- **Composite modules are existential**, in the `exists_installCallTM` style
  (`∃ R entry exit C, …`): a first-return time `t ≤ C·(size)`, no earlier exit, an exact finish
  configuration, and the scratch tapes and heads restored.

The constants are indicative; the statement phase fixes them by execution. Tags: **[now]**
can land on the campaign branch before G1 merges. **[G1-merge]** touches no G1 file but uses
G1's generic statements. **[Catalog/G1]** goes in a G1-owned file, after the G1 gate. **[G2]**
is proposed as a G2 statement. **[rec]** is a record row, filled after G2 and the
Catalog/G1 rows.

| Row | Tag | Statement (probe part) | Contract |
|---|---|---|---|
| **R8.0** transport | **[now]** | `MultiTapeTM.liftSymbols_runFrom` and the rest of §1 (A) | proved |
| R8.0 corollaries | [G1-merge] | `FinTM.bufferTape_map`; the R1 composition (B) | proved |
| **R8.0b** `counterLoopTMVia` | [Catalog/G1]+§12.7 gate (CounterLoop) | `counterLoopTMVia_run_done/_escape` (E) | exact, as §12.7 |
| **R8.1** framed compare | [Catalog/G1] | `compareTM_run_ofCfg {Symbol} [DecidableEq Symbol]` (D) | `∃ δ ≤ min |u| |v|`, exact time `2δ+2`, finish `{d with state := done (decide (u = v))}`, no earlier verdict, trajectory `[pos−1, pos+δ]`. Canonical `compareTM_run` re-derived (body swap); the trace generalizes `catalog_compare_trace` |
| **R8.2** `scanTM δf δb a₀` (two-pass transducer) | **[G2]** | `scanTM_run_ofCfg` (D) | exact `2|w|+2`; interval rewritten to `(scanResult δf δb a₀ w).2`, verdict `done (scanResult …).1`; trajectory `[pos−1, pos+|w|]` |
| **R8.3** `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM` | [Catalog/G1] | `skipTM_run_ofCfg` (D); landed with `skipBackTM_run_ofCfg`, `seekEndTM_run_ofCfg`, `seekStartTM_run_ofCfg` | skip: exact `|w|+1`, head to `pos+|w|+1`. Landed: skip back is skip's inverse, exact `|u|+3` from the next field's first cell to `u`'s; seek end exact `D+1` to `pos+D`, `D = fieldOffset ws |ws|`, `ws ≠ []`; seek start exact `D+4` back to the table start. Nothing written; the seeks stop at two consecutive blanks (table ends) |
| **R8.4** `writeConstTM i w₀` | [G1-merge] (Scan) | `writeConstTM_run_ofCfg` (C) | exact `2|w₀|+2` (executed), old contents arbitrary, head returns |
| R8.4′ `writeAdvTM i w₀` | [G1-merge] (Scan) | landed: `writeAdvTM_run_ofCfg` | writes `w₀` and leaves the head at `pos + |w₀|`, exact `|w₀| + 1`; the advancing round of `expandTM`. Landed cyclic, over `Fin (|w₀|+1)`: it returns to its start state `0`, the counter-loop round shape |
| **R8.5a** `inputCopyTM i` | [G1-merge] (Scan) | `inputCopyTM_run_ofCfg` (C) | from input position 1, exact `2|x|+2` (executed); both heads return in lockstep (no left delimiter needed) |
| **R8.5b** `exists_inputSeekTM` (`Bool`) | **[now]** | (C) | `∃ R … C`; moves the input head to the binary value on a dedicated tape, `t ≤ C·(|w| + pos + p + 1)`; tapes restored |
| **R8.5c** `exists_inputLengthTM` (`Bool`) | statement now; fill after R8.3 (it needs `skipTM` for the width extension) | — | writes `Nat.bits |x|` on a dedicated tape: per input symbol, `incrementTM` with width extension on overflow (`seekEnd` + `writeConst`), `t ≤ C·(|x|+1)` amortized (§12.7 potential) |
| **R8.5d** `inputFoldTM δ a₀` | [G1-merge] (Scan) | — | native scan of the input with a finite fold, verdict `done (x.foldl δ a₀)`, exact `2|x|+2`; the foreign-symbol validator of §0 |
| **R8.5e** `exists_inputCallTM` | [G1-merge] (`Build/InputCall.lean`; needs R8.5a) | — | `inputCopyTM` (at `Bool`, or lifted) + `exists_installCallTM`: a function-level machine on the native input at a clean seam |
| **R8.6** `exists_expandTM pat` (`Bool`); landed as the definition `expandTM` | [G1-merge] (CounterLoop; needs R8.4′) | landed: `expandTM_run_ofCfg` | `counterLoopTM` round = `writeAdvTM pat`; writes `pat` `d` times contiguously; exact `d(|pat|+1) + counterOverhead w (d+1)` |
| **R8.7** record rows | **[rec]** | `exists_recordStepTM`, `exists_recordEqTM` (G); landed with `exists_recordTestTM`; the rest below | first-return form; landed with `yes ≠ no` in each existential |
| **R8.8** `seamCompTM_runFrom_left` (promotion) + `seamCompTM₂_run_ofCfg` | [Catalog/G1] (Seam) | §12.8 note | statement unchanged from the private `seamComp_left` |

**R8.2 replaces fold, map, mark shift and odometer: one row, one trace.** It is proposed **as a
G2 statement**. Its instances:

- **fold:** `δf a γ := (δ a γ, γ)`, `δb` the identity;
- **in-place map** `f`: `δf a γ := (a, f γ)`;
- **head-mark shift right:** `δf prev γ := (mark γ, setMark γ prev)`, the forward delay (the probe
  checks a concrete shift);
- **shift left:** the same delay on the backward pass;
- **record odometer:** a carry transducer;
- **validity checks:** folds.

G2's planned two-tape `copyMapTM`/`transferMapTM` (§13d) are not needed by §12.8: records move
by plain generic `copyTM`. If G2 keeps them, one request: let `merge` take `Option Γ`, so that
blank destinations (scratch) are admitted. **Decision 12.8.5 is honored:** fold, and with it map,
is a Catalog row sharing the R3/G2 trace (`catalog_trace_run`), since G2 lives in Catalog.

**R8.7, the record rows.**

- All are existential modules over `RecSym Q T`.
- **Entry conditions:** the record at tape `0` (`RecordAt`), the scratch tapes `j ≠ 0` blank,
  and the native input `x.map RecSym.digitEmb`.
- **Exit conditions:** heads, input position, scratch and output restored.
- They are built from R8.0/R8.0b, R8.1–R8.5 and R2 seams, with **no private re-trace**.

| Module | Verdict / effect | Composition |
|---|---|---|
| `exists_recordStepTM M upd (hupd : ∀ τ, upd τ none = τ)` (GAP-4, exact text in G) | `yes` and record of `M.step c` with tag `upd τ (M.outputSymbol c)` if `(M.step c).InWindow s`; else `no`, nothing changed; `t ≤ C·(L + |x| + 1)` | read: `scanTM` folds on F0, the tag and the tape fields (scanned symbols and edge flags) via `skipTM`; copy F1 to a dedicated digit tape (`copyTM`), run the lifted `inputSeekTM`, read the input symbol, restore; finite dispatch on `M.tr`; apply: `scanTM` maps (content at the mark, F0, tag) and delay shifts (marks), F1 `±1` by the lifted increment/decrement on the dedicated tape with copy back, clamp from the edge data |
| `exists_recordEqTM` (G) | `yes` iff the two field lists are equal | `k+3` framed compares (R8.1) with `skipTM`s |
| `exists_recordTestTM P` | `P (state, tag)` | two `scanTM` folds |
| `exists_recordValidTM` | `RecordValid` via `recordValid_iff` | `scanTM` folds per field |
| `exists_recordInitTM` | writes `cfgRecord s (initCfg x) τ₀` from `bits (S n)`-style radius digits | `exists_inputLengthTM` (lifted), `exists_expandTM` (lifted) for the window halves, `scanTM` maps, `writeConstTM` |
| `exists_recordNextTM` | next valid record in odometer order, or overflow | `scanTM` carry over all fields + `exists_recordValidTM` filter, under `counterLoopTMVia` |
| `exists_tableAppendTM`, `exists_tableFindTM P` | append at `seekEndTM`; first record satisfying a fold, with an escape if none | `copyTM`, `seekEndTM`, `scanTM`, `counterLoopTMVia` |

#### 4. S1b's machine plan, recomposed (rich)

*Historical (2026-10-14): S1b stopped (fills-6), and its target is proved at ARM level (§14 H12).
The rows this plan uses keep one remaining consumer, B6's window route (rows 17–18).*

**Parameters.** `Γ := RecSym N.State (Fin 3)`, with the tag being the output summary through
its `Fin 3` code (O4), and `e := RecSym.digitEmb`. The host is a `FinTM Γ`.

**Tapes:**

- `Tab`, the table;
- `Cur₀` and `Cur₁`, the successor workspaces;
- scratch for the record modules;
- dedicated digit tapes: `Rad` (radius), `Len`, `Cnt` (the outer counter, last tape) and
  `Cnt'` (inner loops);
- the lifted constructor's bank and capture tape.

1. **Validate** with `inputFoldTM`. On a foreign symbol, emit `e false` and halt. This is needed
   only for space, but it is cheap.
2. **Radius.** Run `M_S.liftSymbols e` under generic `embedSilentRetTM` with its output
   captured on `Rad`, then rewind. Time at most `M_S.configBound n (a·S n)`
   (`of_spaceUsed_le` plus `liftSymbols_runFrom`).
3. **Window template.**
   - Lifted `exists_expandTM` with counter `bits (S n)` and pattern `false^{c₀}` writes the left
     half.
   - `writeConstTM [.cell none true]` writes the center.
   - `expandTM` again writes the right half.
   - A `scanTM` map turns the digits into `.cell none false`.

   No multiplication by `c₀` is needed: the pattern length carries it.
4. **Initial record.** `exists_recordInitTM` writes it, plus a one-digit flag field `[digit
   false]` ("unprocessed").
5. **Outer counter.** Copy the template fields `c_N` times onto `Cnt` (`copyTM` + `skipTM`),
   then map every cell to `digit true` (`scanTM`). Its value `2^{c_N·W} − 1` exceeds the record
   count `V` with `c_N := ⌈log₂(3(|Q|+1))⌉ + 4`. Here `W` is the record's cell count, and the
   proof uses `2^{posWidth n} ≥ n+2` and `8^{2s+1} ≥ 3^{2s+1}(2s+1)`.
6. **BFS** with `counterLoopTMVia e Round a (some ex)`. A round:
   - `exists_tableFindTM` finds the first record with flag `false` (escaping to `ex` if none),
     and copies it to `Cur₀` and `Cur₁`;
   - `exists_recordStepTM (N.fixChoice false)` runs on `Cur₀`, and
     `exists_recordStepTM (N.fixChoice true)` on `Cur₁`. The upd is the summary's append table
     on the code;
   - for each `yes`, an inner `counterLoopTMVia` over the table with `exists_recordEqTM`
     decides membership, and `exists_tableAppendTM` appends a new record with flag `false`;
   - the processed record's flag is set (`scanTM` map), the workspaces are cleared
     (`clearTM`), and the table head is rewound (`seekStartTM`).

   Both exits are wired by R8.8.
7. **Verdict.** `exists_tableFindTM (accept)` scans for a record with state `none` and tag
   `accept`. Emit `e true` or `e false`, then halt.
8. **Finish.** `alphabet_reduction` gives a `FinTM Bool` within `c·(T + 1)`.
9. **Correctness** is §12.8's chain, with `cfgRecord_inj` in place of the bit codec:
   - `T := Fin 3` identifies records with `coreSum`s;
   - note-6's bridge applies, the outside-window rejection being `recordStepTM`'s `no`;
   - S1a's four lemmas finish.
10. **Time.**
    - `counterLoop_time_le` gives `V·B + 4V + 2|w| + 2`, with `B = O(V·(L+F) + n)` from the
      nested table loop.
    - Add the startup terms: the constructor bound, `O(S n)`-cost expansions, and
      `O(n log n)` input length.
    - Then `alphabet_reduction`'s `c(T+1)`. The result is at most `K·2^{c'(S n+1)}`.
    - Every budget is evaluated at `n`; no monotonicity of `S` is used.

#### 5. Sequencing — what can be issued before the G1 gate closes

| Item | Lands | Blocked on |
|---|---|---|
| **R8.0 transport** (`SymbolLift.lean`) | **now**. The probe's Part A *is* the proof; a maintainer pre-issue landing or a tiny batch | nothing |
| **R8.5b** `exists_inputSeekTM` (`Bool`; composed of `copyTM`, `timed_rewind`, `counterLoopTM`, `clearTM`, all public at HEAD) | **now**, as a statement phase plus a fill batch | nothing; it lifts to rich hosts by R8.0 |
| R8.5c, R8.5e, R8.6 (`Bool` rows needing Scan or seek) | statements now; fills after the G1 merge (R8.5e, R8.6) or after R8.3 (R8.5c) | G1 merge / R8.3 |
| Statements of **everything else** | **draft now** (this document, probe green on `s13d/g1`) | — |
| R8.0 corollaries, R8.4, R8.5a/d, the `CfgRecord` pure layer | after **G1 merges** (no G1 file edited) | G1 gate; CfgRecord's `InWindow` also on C1d |
| R8.1, R8.3, R8.8 | after the **G1 gate**, in Catalog/Seam | G1 gate; coordinate with G2/G4 (one trace) |
| R8.2 `scanTM` | with **G2** | G1 gate; G2's statement phase adopts it |
| **R8.0b** `counterLoopTMVia` | after the **G1 gate and the §12.7 fill gate** | both gates |
| R8.7 record rows | after the R8.2 fill (G2) and the R8.1/R8.3 fills | G2 fill |
| S1b | after R8.7 | — |

**The sequencing change versus the note:** R8.0b is new, and it sits on two gates (G1, §12.7).
It is the long pole for every rich consumer, since no rich loop exists without it. Some things
can be issued before the G1 gate closes:

- R8.0, which the probe proves;
- R8.5b;
- the statement phase of every other row (the probe is green on `s13d/g1`).

The critical path is then the G1 gate, then R8.0b with R8.2 (G2) and R8.1/R8.3, then R8.7,
then S1b. Two items that the note called "landable now" in fact need the G1 merge, because
their statements use the generic `bufferTape`: `writeConstTM` and the input rows. `expandTM`
needs the advancing writer R8.4′.

#### 6. Per-consumer rows (updated)

| Consumer | Rows |
|---|---|
| **S1b** | §4: R8.0, R8.0b, R8.1–R8.5, R8.6, R8.7 (step, eq, test, init, table rows), R8.8, `alphabet_reduction` |
| **Savitch** | Rich records with binary F1 (`O(S)` cells); frame stack on a rich tape; R8.7 `recordStepTM` (both choice bits) + `recordEqTM` for adjacency; `recordNextTM` + `recordValidTM` for midpoints; R8.3 over frames; `copyTM`/`clearTM` at fixed intervals (note 7); R8.0b loops; R8.8; R8.5d validation; `alphabet_reduction_spaceUsed` |
| `spaceConstructible_*` | `Bool` only: R8.5c, R8.6, `incrementTM` |
| `PATH_NLComplete` (hardness) | ARM engine (12.8.4); no §12.8 row |
| `PATH_mem_NL` | R8.5b, once the nondeterministic host exists (SC-3; superseded 2026-10-13: C2 is written as programs, §16b item 4) |
| Space hierarchy | **Superseded 2026-10-12 by the window route** (§16b item 3; the RD-3 statement gate, minor 2): R8.7's initial-record, test and step rows under a configuration-count clock (`counterLoopTMVia`), through H2, H3 and H5, with R8.5d for input validation. The earlier route (R8.0b's budget loop, R8.8's success/cap exits, R8.1's budget comparison, `clearTM` resets, and no R8.7) is dropped |
| `TQBF_mem_PSPACE` | R8.2 (validation folds, clause evaluation, the trit odometer), R8.5b (input re-reads), R8.3 |
| `NP_subset_PSPACE` | `incrementTM`, `vhostEmitTM`, R8.8 |
| **G3/G4 (§13d)** | R8.3 (zone scanning across separators), R8.2 (per-track maps), R8.0 (Bool counters on `ZoneSym` tapes via `e := Sum.inl`) |

#### 7. Open decisions

- **O1, transport home.** New `TuringMachine/SymbolLift.lean` (recommended), or CounterLoop's
  `SymbolTransport` section (during its open gate).
- **O2, R8.0b route.** In-place proof generalization with the `Bool` contracts re-derived by Z5
  (recommended; one round induction). The alternative is a second host with its own induction,
  which is a duplicated trace.
- **O3, `scanTM` as a G2 statement.** It needs G2's agreement. Separately, the optional
  `merge : Option Γ → Δ → Γ` request for `copyMapTM`.
- **O4, the S1b tag type.** `Fin 3` code (recommended; no frozen-surface change), or a sanctioned
  `Fintype OutSummary` export in ConfigGraph.
- **O5, table seeks.** `seekEndTM` and `seekStartTM` (double-blank stops) in the skip family, or
  as `counterLoopTMVia` loops over `skipTM` (slower, no new row).
- **O6, input validation (R8.5d).** Mandatory for rich space-bounded consumers. Confirm, or
  require every rich row's space bound to be input-independent instead (harder to state).
- **O7, R8.0 now.** Whether the transport lands as a maintainer pre-issue lemma, since the
  probe proof is complete (one file, about 120 lines), or through a statement gate plus fill
  like the other §12 rows.

#### 8. Decisions and the landed statement layer (2026-10-11)

**Decisions.**

- **User:** O2, generalize `counterLoopTM` in place, with the `Bool` contracts
  re-derived by Z5 (R8.0b, a later batch; target signatures below); O3, G2 is
  `scanTM`; O7, the transport lands by PR plus the §12.8 statement gate.
- **Maintainer:** O1, `TuringMachine/SymbolLift.lean` (landed, PR #16); O4, the
  `Fin 3` tag code; O5, dedicated `seekEndTM`/`seekStartTM` rows; O6, input
  validation (R8.5d) is mandatory for rich space-bounded consumers.

**Landed** on `integrate/s12-8-statements` (campaign `5e438f50` with PR #16,
merged at `b28e22ea`). Every machine and carrier is a real definition. Every
contract is sorried with a proof sketch, except the two results already
proved, which keep their proofs: `seamCompTM_runFrom_left`, promoted verbatim,
and `cfgRecord_length`. There are 25 new sorries. Records:
`campaign/gates/s12-8-statements/logs/` and
`campaign/items/s12-8/S128StatementsPreship.lean.txt`.

| Row | File | Landed declarations | Contract |
|---|---|---|---|
| one-tape actions | `Build/Catalog.lean`, Part 3 | `tapeAction`, `inputMoveAction` | the transition-table vocabulary of every §12.8 machine |
| field layout | Catalog, Part 3 | `joinFields`, `fieldsTape`, `fieldOffset`, `fieldsTape_field` | each field is a §12.6 delimited word in place |
| R8.1 | Catalog, Part 3 | `compareTM_run_ofCfg` | as drafted |
| R8.3 | Catalog, Part 3 | `SeekPhase`; `skipTM`, `skipBackTM`, `seekEndTM`, `seekStartTM`, each with `_run_ofCfg` | as in the §3 row, with trajectories |
| R8.2, the G2 core | Catalog, Part 3 | `mealyRun`, `scanResult`, `ScanPhase`, `scanTM`, `scanTM_run_ofCfg`; the steps `scanKeep`, `scanFold`, `scanMap`, `scanShift`, `scanCarry`; the identities `scanResult_fold`, `scanResult_map`, `scanResult_shiftRight`, `scanResult_shiftLeft`, `scanResult_carry` | the scan contract as drafted. The instances are pure identities of `scanResult`, so the scan keeps one framed contract |
| R8.4, R8.4′, R8.5a, R8.5d | new `Build/Scan.lean` | `WritePhase`, `writeConstTM`, `writeAdvTM`, `inputCopyTM`, `inputFoldTM`, each with `_run_ofCfg` | constant writer `2|w₀|+2`; advancing writer `|w₀|+1`, cyclic; input copy and input fold `2|x|+2` from input position `1` |
| R8.5e, R8.5b | new `Build/InputCall.lean` | `FinTM.exists_inputCallTM`, `exists_inputSeekTM` | first-return modules |
| R8.6 | `Build/CounterLoop.lean` | `expandTM := counterLoopTM (writeAdvTM k i pat) 0 none`, `expandTM_run_ofCfg` | exact `d(|pat|+1) + counterOverhead w (d+1)`, with `d` copies of `pat` from `pos` |
| R8.7 | new `Build/CfgRecord.lean` | `Cfg.InWindow` (relocated verbatim from `ClassPSPACE/TQBF.lean`, which now imports it); `RecSym`, `recSymFintype`, `RecSym.digitEmb`, `binDigits`, `posWidth`, `cfgRecord`, `cfgRecord_length` (proved), `cfgRecord_inj`, `RecordValid`, `recordValid_iff`, `RecordAt`; `exists_recordStepTM`, `exists_recordEqTM`, `exists_recordTestTM` | first-return modules with distinct verdict anchors |
| R8.8 | `Build/Seam.lean` | `seamCompTM_runFrom_left` (promoted), `seamCompTM₂`, `seamCompTM₂_run_ofCfg` | one continuation per exit, each run unboundedly after the dispatch step |

**Changes from the draft.** Each was executed in the pre-ship probe where
executable.

1. **`yes ≠ no`** is part of every record row's existential. Without it, a
   module with `yes = no` satisfies `exists_recordEqTM` vacuously, and no
   consumer could branch on the verdict.
2. **The field layout lives in Catalog**, not in CfgRecord, because the seek
   rows' contracts are stated over it. CfgRecord imports Catalog and
   `SymbolLift`, not CounterLoop, since R8.0b is not in this step. TQBF's
   import closure gains Catalog, `SymbolLift` and CfgRecord; there is no
   cycle.
3. **`writeAdvTM` is cyclic** over `Fin (|w₀|+1)`. It returns to its start state
   `0`, so it is a counter-loop round as it stands. A seam caller that runs it
   once uses `seamReleaseTM`.
4. **R8.6 is the concrete `expandTM`** with an exact contract, not an
   existential.
5. **The seek family.** Skip back is the inverse of skip (`|u|+3`, from the
   next field's first cell), not its mirror. The seeks' exact times are `D+1`
   and `D+4`, with `D = fieldOffset ws |ws|`. Every row carries the §12.6
   trajectory clause.
6. **No new copier phase type.** The input copier reuses `SweepPhase`, and the
   input fold reuses `ScanPhase`.
7. **The scan instances** are stated as identities of `scanResult` rather than
   as five machine contracts. `scanTM_run_ofCfg` turns each into the
   instance's run.
8. **`Cfg.InWindow`** replaces the probe's `WindowedP`.
9. **One-tape actions.** The §12.8 machines' tables are written with two
   named actions, `tapeAction` and `inputMoveAction`, instead of literal
   `Action` tuples. With literal tuples, the copy-text screen found 17 new
   cross-file pairs: the input copier and the input fold against the R3
   sweeps and the scan. With the helpers there are none. Twelve new same-file
   pairs remain: the four seek tables among themselves, and the two writers.
   These are distinct small machines sharing their phases, not copied
   proofs. The proved R3 tables are unchanged.
10. **Not landed**, being outside this step:
    - `FinTM.bufferTape_map` and the other R8.0 corollaries;
    - R8.5c, `exists_inputLengthTM`;
    - R8.0b;
    - the record rows `exists_recordValidTM`, `exists_recordInitTM`,
      `exists_recordNextTM`, `exists_tableAppendTM` and
      `exists_tableFindTM`. Their statements need S1b's table layout (a
      header, the radius digits, the odometer order) and a template tape
      holding the widths a validity machine compares against.
11. **`MultiTapeTM.liftSymbols_step` is public** in the landed
    `SymbolLift.lean` (PR #16), as the transport's one-step form; §1 above
    made it private. Only `moveInputPos_cast` is private.

**R8.0b target signatures.** These land in a later batch, after this
statement gate. Home `Build/CounterLoop.lean`, which then imports
`SymbolLift`.

```lean
def lastEmb (k : ℕ) : Fin 1 ↪ Fin (k + 1) := ⟨fun _ => Fin.last k, fun a b _ => Subsingleton.elim a b⟩
def counterLoopTMVia {k : ℕ} {Γ S : Type} [DecidableEq S] [DecidableEq Γ] (e : Bool ↪ Γ)
    (M : MultiTapeTM k Γ S) (a : S) (exit : Option S) : MultiTapeTM (k + 1) Γ (CounterLoopState S)
  -- .body s : ((embedEmitTM Fin.castSuccEmb M).tr s inp work).mapState (counterLoopRedirect a exit)
  -- .dec f  : ((embedEmitTM (lastEmb k) ((decrementTM 1 0).liftSymbols e)).tr f inp work).mapState
  --             (counterLoopDecExit a)
  -- .done, .escape : stationary
-- generalized in place (types only, bodies verbatim; existing call sites unchanged):
def counterLoopCfg {k : ℕ} {Symbol S : Type} {x : List Symbol} (q : Option (CounterLoopState S))
    (c : Cfg k Symbol S x) (ct : ℤ → Option Symbol) (cp : ℤ) : Cfg (k + 1) Symbol (CounterLoopState S) x
def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)
    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x
theorem counterLoop_time_le {k : ℕ} {Symbol S : Type} {x : List Symbol} … -- otherwise verbatim
-- the generic contracts are counterLoopTM_run_done / counterLoopTM_run_escape verbatim, with
--   M, τ, c over Γ; ct : ℤ → Option Γ; counterLoopTM M a exit ↦ counterLoopTMVia e M a exit;
--   hw : ∀ p : ℤ, -1 ≤ p → p ≤ (w.length : ℤ) → ct (cp + p) = FinTM.bufferTape (w.map e) p,
--     for the counter word w : List Bool;
--   done finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ) then some (e true) else ct q;
--   escape finish counter: fun q => if cp ≤ q ∧ q < cp + (w.length : ℤ)
--     then FinTM.bufferTape ((counterWord w (r₀ + 1)).map e) (q - cp) else ct q;
--   all four clauses kept (finish, no earlier exit, counter head range, body heads).
theorem counterLoopTMVia_run_done …
theorem counterLoopTMVia_run_escape …
-- counterLoopTM and its two contracts: statements byte-identical; proofs re-derived at
-- e := Function.Embedding.refl Bool through MultiTapeTM.runFrom_eq_of_agreeOn (Z5), the
-- decrement tables agreeing pointwise (decodeBool refl γ = some γ, Option.map refl = id).
```

**Governance.** Catalog and Seam are G1-owned files, and `scanTM` is the G2
core of the §13d revision. Under the §13d rule this branch therefore lands by a
PR the user merges, with its own statement gate. Nothing is pushed by the
agent.

**Open questions for the statement gate.**

1. **Skip back.** Is the inverse convention right (from the next field's
   start, `|u|+3`), or should it be the mirror of skip (from a word's last
   cell, `|u|+1`)?
2. **The empty table.** `seekEndTM` requires `ws ≠ []`, since an empty table's
   end is its start. Should tables carry a header field, so that every seek
   precondition is uniform?
3. **The cyclic writer.** Is `writeAdvTM`'s anchor-equals-start shape
   acceptable, or should it have a stationary `done` with the loop adapting
   it?
4. **Tape layouts of the record rows.** `exists_recordStepTM` has
   `K + 1` existential tapes with the record on tape `0`; `exists_recordEqTM`
   has 2 tapes; `exists_recordTestTM` has 1. Hosts embed them by R1. Is the
   fixed layout acceptable, or should each row take a tape selection? The
   step row's fill will also import InputCall, for the input seek, which
   enlarges TQBF's import closure again.
5. **The deferred record rows.** Should validity, init, next and the table
   rows enter this gate, or S1b's statement phase, once the table layout is
   fixed?
6. **The facade.** Scan, InputCall and CfgRecord are not wired into the
   `TuringMachine` facade, following the precedent of `SymbolLift`,
   CounterLoop and Zone. Is facade wiring wanted at this gate?
7. **G2's agreement** to `scanTM` as its core, and whether the planned
   `copyMapTM`/`transferMapTM` are still wanted. §12.8 does not need them.

#### 9. Statement gate, round 1: decisions and repairs (2026-10-11)

Round 1 failed with 0 blockers, 1 major, 7 minors and 39 notes
(`campaign/gates/s12-8-statements/findings.md`).

**Decisions** (user, the auditor's recommendations, on the open questions
of §8):

1. Skip back stays the **inverse** of skip, at `|u| + 3`.
2. Shared tables get a **fixed nonempty header field**, so seek end always
   has a field to stop after. The table ends are two blank cells before the
   header and two after the last field. From seek end's stopping blank, a
   consumer reaches the table start by skipping back over the last field
   and then seeking start. The deferred table rows are stated with this
   layout.
3. `writeAdvTM` stays **cyclic**. One-shot callers use `seamReleaseTM`.
4. The record rows keep their **fixed local tape layouts**, and hosts embed
   them by R1.
5. The deferred record rows (validity, init, next, table append and find)
   get **their own statement gate** with S1b's concrete layout, before
   S1b's fill uses them. R8.0b and R8.5c are explicit prerequisites.
6. The new modules are **wired into the `TuringMachine` facade** at this
   gate: `SymbolLift`, `Build/CounterLoop`, `Build/Scan`, `Build/InputCall`
   and `Build/CfgRecord`. Nine older files of the topic are also absent
   from the facade; they are recorded as `backlog.md` FAC-1.
7. G2's core is `scanTM`, and `copyMapTM`/`transferMapTM` stay for G3/G4
   (§13d, G2).

**Repairs** (for round 2):

- **Major 1: work-space clauses.** The record rows and the input seek
  bounded time but not the cells they visit, so they were too weak for
  Savitch and logspace consumers. Each now bounds every work head, through
  its verdict or exit, to `C·(size + 1)` cells of its entry position. The
  size is the record's layout length for the step and test rows, `fs`'s
  layout length for the equality row, and `|w|` for the seek. So the space
  does not depend on how far the native input head travels, and repeated
  calls compose. The step row's sketch now names the obligations the auditor
  identified: save and restore the host's input position in binary, and
  clamp the position field at `0` and `|x| + 1`.
- **Minor 2.** The input seek's rewind: `timed_rewind` stops at position
  `1` within `pos + 2` steps, and one left move follows.
- **Minor 3.** The input call's first-return clause splits on whether the
  callee's entry equals its exit. If it does, `seamReleaseTM` supplies a
  fresh entry first.
- **Minors 4, 5 and 6.** `recordValid_iff`'s validator needs width
  templates. A record determines the configuration *core* together with the
  tag. `fieldOffset`'s end formula needs `fs ≠ []`.
- **Minors 7 and 8.** Corrected in the records: the declfreeze log
  miscounted the promotion's citations (3, not 4), and Catalog's ledger
  denominator is now 459.

### 12.8b Record tables, the deferred record rows and R8.5c (statements landed 2026-10-11; design W1 accepted by the user as drafted)

**Why.** §12.8a §8 item 10 deferred five record rows. Their statements need S1b's table layout,
the radius digits, the odometer order, and a template that the validity machine compares
against. §12.8a §9 decision 2 fixed the table convention:
- a nonempty header;
- two blank cells before it, and two after the last field;
- an end-to-start adapter.

Decision 5 sent the deferred rows to their own gate. This increment states that layout, the
five rows, R8.5c, and three small additions the rows and their consumers need.

**Homes.**

| Module | Imports | Contents |
|---|---|---|
| `Build/InputLength.lean` | `Build/CounterLoop` | R8.5c, `exists_inputLengthTM`, alone |
| `Build/RecordTable.lean` | `Build/CfgRecord`, `Build/Seam`, `Build/InputLength` | the layout lemmas, the record template, tables, the adapter, field copy, find and append, and the template, init, validity and next rows |

- R8.5c gets its own small module so that the constructibility files can use it without the
  record layer. 12.2c may fold it into `InputCall`.
- No in-flight file was touched, the imports are acyclic, and TQBF's closure is unchanged.
- Both modules are wired into the `TuringMachine` facade.

**Layout.**

| Declaration | Meaning |
|---|---|
| `tableFields h es` | `h :: es.flatten`, the header then the entries' fields |
| `TableAt d r o h es` | the cells `[-2, L+1]` around origin `o` show `fieldsTape (tableFields h es)` |
| `TableWF m h es` | a nonempty header; every entry has `m` nonempty fields |
| `tableOffset h es j` | where entry `j` starts |
| `recordLength k n s` | `k(2s+1) + posWidth n + k + 4`, the length of every valid record |
| `recordTemplate Q T n s` | the bound field `bits (n+1)` and a window of `2s+1` cells |

- `TableAt` is anchored at an origin, not at the head, because find moves the head and append
  changes the table.
- `TableWF` keeps double blanks at the two ends only, so the seek rows apply.
- `tableOffset` has a closed form, and at `j = |es|` it is the second trailing blank, where
  `seekEndTM` stops.
- `recordTemplate` carries what a candidate record cannot reveal.
- `recordValid_iff_exists_cfg` is the bridge Savitch needs: valid records are exactly the
  records of windowed configurations on the actual input.
- `tableRewindTM` is the adapter, as a real machine: `skipBackTM` then `seekStartTM`,
  R2-seamed, with an exact contract (time `D + 7`).

**Rows.** Every row follows the §12.8 gate conventions:
- an existential module;
- `yes ≠ no` for two-verdict rows;
- a first-return time bound;
- an exact finish that restores every head, the input position, the scratch and the output;
- the work-space clause `∀ u ≤ t, ∀ j, |pos_u j − pos_0 j| ≤ C·(size + 1)`;
- fixed local tape layouts hosted by R1.

| Row | Finish | Time |
|---|---|---|
| `exists_inputLengthTM` | `Nat.bits \|x\|` at the output head | `C(\|x\|+1)` |
| `exists_fieldsCopyTM m` | the source's field layout at the destination head | `C(L+1)` |
| `exists_tableFindTM e m δ a₀ acc` (`0 < m`) | the first entry satisfying the fold predicate, by `findIdx?`: `yes` with the head on it, or `no` with nothing changed | `C(L_tab + \|w\| + 1)` |
| `exists_tableAppendTM m suf` | the table extended by one entry | `C(L_tab + L_e + 1)` |
| `exists_recordTemplateTM` | `recordTemplate \|x\| s` | `C(L_tpl + \|ws\| + \|x\| + 1)` |
| `exists_recordInitTM` | `cfgRecord s (Cfg.init q₀ x) τ₀` | `C(L + \|ws\| + s + \|x\| + 1)` |
| `exists_recordValidTM` | `yes` iff `RecordValid`, nothing changed | `C(L_fs + L_tpl + n + 1)` |
| `exists_recordNextTM` | `first`/`next` over an existential duplicate-free enumeration of exactly the valid records | `C ^ (L + L_tpl + 1)` |

**Decisions** (the design's Q1–Q9, as drafted; the user accepted the draft on 2026-10-11, and the statement gate audits them):

1. **Existential order.** The enumeration order of `recordNext` is existential. Savitch needs
   only a duplicate-free walk of exactly the valid records, and an explicit order would need
   a rank of `Option Q` and `T`, which no consumer reads. The fill uses the carry odometer.
2. **Fuel.** Find takes fuel `|es| < val w` and restores it, because the number of entries is
   on no tape and the only rich loop host needs a counter. A dedicated scanner would be a
   second forward trace, against decision 12.8.5.
3. **R8.5c's route.** It uses a dedicated framed counter whose carry writes `true` on the
   first non-`true` cell, the blank delimiter included. That is the counting phase of
   Catalog's private `f2_counterTM`, framed. The pair goes to the duplication ledger for the
   12.2c window. (§12.8a's "increment with width extension" fails, because `seekEndTM` stops
   one cell past the delimiter.)
4. **Validity time includes `n`.** No public row compares two words by `≤`. The bound
   `v ≤ n+1` uses the `Bool` `counterLoopTM`, lifted onto two digit tapes, at cost `O(n)`.
   Space stays `O(L + L_tpl)`.
5. **The three additions are rows:** `fieldsCopy`, `recordTemplate` and the adapter. There is
   no `tableMem` row; S1b keeps its inner loop.
6. **Homes** as above, with facade wiring at landing.
7. **Input convention.** The rows that read the native input enter at position `1` and
   restore it, as `inputCopyTM` and `inputFoldTM` do. Contrast `recordStepTM`, which saves and
   restores an arbitrary position.
8. **`recordNext`'s exponential bound** is honest: gaps between valid records are exponential,
   and `ComputesInSpace` needs only halting.
9. **The table rows are generic over `Γ`.** Find takes `e : Bool ↪ Γ` for its counter.

**Degenerate cases** (checked in the statements or executed by the probe):
- find at `m = 0` would be false, since `tableFields h [] = tableFields h [[]]`; hence `0 < m`;
- validity needs `|fs| = k + 3`, without which the verdict is not a function of the tape;
- the empty table;
- `T` empty: `first` answers `no` through `match`;
- `k = 0`, `s = 0` and `n = 0`.

**Consumers.**
- **S1b (§12.8a §4):** the template, the counters, the initial table, the round's find,
  copy, step, membership and append, and the verdict find.
- **Savitch:** the template, the start vertex, the midpoint enumeration, adjacency through the
  landed step and equality rows, and frame push and pop. Every frame is `O(S n)`.
- **The constructibility files:** `exists_inputLengthTM`.

**Fill dependencies.**

| Rows | Need |
|---|---|
| find and next | R8.0b |
| adapter, fieldsCopy and append | the Catalog Part-3 fill (delivered, PR #42) |
| template, init and valid | R8.5c and R8.6 |

Evidence: `campaign/gates/wave1-statements/evidence/S128bStatementsProbe.lean.txt`, which runs the design's
executed checks against the landed definitions.

### 12.9 Oracle-machine rows (landed 2026-10-11 with epoch B1; `Build/OracleCall.lean`)

**Why.** Every §12 row is plain-machine level, and the oracle model (`TuringMachine/Oracle.lean`)
had no run algebra. The B1 one-query constructions needed three capabilities: (i) a computation
captured onto the **query tape** and submitted; (ii) the four-state **answer tail**; (iii) a way for
plain contracts to drive an oracle machine.

**Rows.**

- In `Oracle.lean`:
  - the run algebra: `step_of_halt`, `runFrom_succ_eq_step'`, `runFrom_add`, `runFrom_of_halt`,
    `runFrom_comm_of_step`, `ComputesInTime.mono`/`output_unique`;
  - the extraction contract: `queryString_length_le_of_blank` (C1-P1) and `queryString_eq_of_cells`;
  - **the transfer bridge** `runFrom_eq_plainEmptyOracle`, after `runFrom_eq_of_forall_ne_qQuery`.
    On a run segment that avoids `qQuery`, the oracle run is the run of the plain table
    `plainEmptyOracle`, so host-parametric plain contracts apply unchanged.
- In `OracleFinite.lean`: the bundled `mono` and `output_unique`.
- In `Build/OracleCall.lean`:
  - `queryString_bufferTape`;
  - `answerAction`, with `step_of_qQuery`, `step_of_answerAction` and `runFrom_two_of_qQuery`;
  - **query capture** `capture_reaches_qQuery`: W1 with its return state taken to be `qQuery`.
    W1 writes on the host's last tape, which is the query tape.
- In `Finite.lean`, the shared guard discharge: `MultiTapeTM.exists_first_halt`.

**Consumers.**

- `mem_POracle_of_polyTimeReducible`, and through it the `SAT`-oracle corollaries and
  `EXP_subset_POracle_EXPCOM` (B5);
- `unaryWitnessLang_mem_NPOracle`, using the tail through `OracleNDTM.fixChoice`;
- `compl_mem_POracle`, using `runFrom_comm_of_step`.

**Not yet here: oracle-call hosting.** This is a plain host simulating an oracle machine that runs
a decider on the extracted query word. It is the library gap behind `POracle_eq_P_of_mem_P`
(deferred) and B5's `NPOracle_EXPCOM_subset_EXP` dispatcher. Its rows need a design note and a
statement gate:

- the headline simulation;
- the private clean call of `ClassNP/EXP.lean` promoted, without the native-input rewind;
- origin tracking for the query tape;
- query extraction with cell `-1` saved;
- the dispatch host.

The draft headline statement, `FinOracleTM.exists_plain_simulation`, is recorded in
`campaign/fills/b1/integration/b1-integration.md`. **Designed and stated in §12.10** (2026-10-11).

### 12.10 Oracle-call simulation (statements landed 2026-10-11; design W2, route and homes accepted by the user)

**Why.** §12.9 records the gap, "not yet here: oracle-call hosting". No public row lets a
plain host simulate an oracle machine by running a decider on each extracted query. Two
targets are blocked:
- B1's last, `POracle_eq_P_of_mem_P`;
- B5's summit, `NPOracle_EXPCOM_subset_EXP`, and through it three `EXPCOM` identities and
  `baker_gill_solovay`.

**The decision: one trace, and nondeterminism by choice words.**
- **The deterministic row is the only oracle-call simulation trace.** It is a plain host that
  answers each query by a clean call of the decider.
- **The nondeterministic form is a reduction, not a second simulation:**
  1. the choice-word machine determinizes the oracle NDTM along a word on a work tape;
  2. the deterministic row simulates it;
  3. the plain certificate shell and the proved `exists_proj_decider` enumerate the words.

  The total is `2^O(p)`.
- **Branchwise simulation is rejected.** Branches would consume choice bits through every
  decider run, so the only public determinization would enumerate doubly exponentially many
  words. Avoiding that needs a sparse-guess row, which is a second trace under another name.
- **Virtual input stays at the plain level, after the simulation.** An oracle machine has one
  `qQuery` state, so an oracle-level Z1 would re-prove Z1's lockstep. This forces the
  deterministic row to be stated **from preloaded starts**. The `initCfg` form, the B1b draft
  headline, is a proved corollary.

**Rows.**

| Module | Declaration | Status |
|---|---|---|
| `Build/OracleSim.lean` | `FinTM.prefixWords` (+ `_nil`, `_update`), `Cfg.init_eq_ofWords`, `OracleTM.queryString_runFrom_length_le_of_blank` (W2-0) | proved |
| | **`FinOracleTM.exists_plain_simulation`** (W2-S): from any preloaded start, a plain host reproduces the oracle machine's halting output within `a·(t+1)² + a·Σ_{r<t} [query at r]·τ(\|query_r\|)` | **proved** (fills-4 to fills-6; wave-1 fill gate closed 2026-10-12) |
| | `…_of_monotone`, `…_initCfg`, `FinOracleTM.exists_plain_decider` | proved from W2-S |
| | `FinOracleNDTM.choiceOut`, `choiceOut_eq_true_iff`, `mem_iff_exists_choiceOut` | proved |
| | **`FinOracleNDTM.exists_choiceTM`** (W2-C): the choice-word machine, `≤ 2\|u\| + 2` steps, the same queries, except that at exhaustion in the query state one query may be submitted and its answer discarded (statement gate, minor 4) | **proved** (fills-4) |
| `Build/CertShell.lean` | **`FinTM.exists_certificateShell`** (W2-V): the plain shell deciding `{x ++ u \| \|u\| = C(\|x\|+1)^c ∧ out x u = [true]}` | **proved** (fills-4) |
| | `FinTM.certificateShell_proj` | proved |

- The exact sum, "`T_D` of the query lengths", needs no monotonicity.
- Both instantiations follow from the monotone corollary:
  - polynomial `τ` gives `P^O = P`;
  - exponential `τ`, at a polynomial-time machine, gives `P^EXPCOM ⊆ EXP`, and the summit
    follows through W2-C.

**Fill routes** (binding sketches in the docstrings).
- **W2-S:**
  - the source's tapes, a shadow tape tracking the query head's side of the origin, the Z1
    bank of the clean call `exists_installCallTM`, and a scratch tape;
  - off `qQuery`, the bridge `runFrom_eq_plainEmptyOracle` plus Z5;
  - at `qQuery`, nine R2-seamed phases: bookmark, origin walk, save and blank cell `-1`,
    `copyTM`, the Z1 call at `y = []`, read the verdict, restore, walk back, answer.
  - **As delivered** (fills-6; documented in the target's appendices, and confirmed sound and no
    weaker by the wave-1 fill gate): the host `oracleHost` is **one public phase host**
    (`phaseHostTM`), with a single R2 seam between the public copy and the relocated call
    (`oracleService_run`). Preparation takes at most `natAbs p + 3` steps and restoration
    exactly `natAbs p + 3`, for both signs of the displacement and for zero. A query costs at most
    `2·|p| + 2·|z| + tCall + 13`, redirects included.
- **W2-C:** lockstep by induction on `u`, in the `toOracleNDTM_runWith` shape. An exhausted
  word answers `false`, so an unhalted branch never shows `[true]`.
- **W2-V:** the native-input call R8.5e (`exists_inputCallTM`) at `splitSolve`, then Z1 inside
  the **returning** R1 capture, then a three-state scan. R8.5e is proved at the tip since PR
  #41, so W2-V's route cites no sorried row.

**Decisions.** The user took the first and third (2026-10-11); the rest are as drafted and
go to the statement gate.

1. **The route:** one trace, choice-word enumeration, no branchwise row.
2. **W2-S in preloaded generality,** with the `initCfg` form derived.
3. **W2-V in its own plain module,** `Build/CertShell.lean`, keeping plain consumers off the
   oracle module. Deduplicating the private 2B shell in `ntime_poly_subset_NP` is the shell's
   second customer, a 12.2c item.
4. **W2-C is public here.** It is the core of a relativized Theorem 2.6. It has one named
   customer, against the rule of admission's two.
5. **Time only.** The oracle layer has no space measure. This is flagged against the §12/§13
   space mandate.
6. **Sequencing.** W2-S and W2-C can be filled at once; W2-V's sorried dependency is gone.

**Mirrors, factored** (disclosed at landing; factored in round 2 of the wave-1 statement gate,
2026-10-11, user decision; `campaign/gates/wave1-statements/resolutions.md`):
- W2-0 and the private invariants `runFrom_workTapes_invariant` (`Oracle.lean`) and
  `runWith_headBlank` (`OracleNondeterministic.lean`) now all specialize the promoted
  `OracleTM.step_radius`/`OracleTM.runFrom_radius` (`Oracle.lean`).
- `certificateShell_proj` and `Nondeterminism.lean`'s split callers cite
  `append_split_unique` with `certificateLength_strictMono` or
  `expCertificateLength_strictMono` (new module `ChoiceWords.lean`). The private split lemmas
  are deleted.
- `mem_iff_exists_choiceOut` and `Nondeterminism.lean`'s acceptance argument share
  `choiceBudget_le` and `run_take_of_halted` (`ChoiceWords.lean`).

**Consumers** (derived in `campaign/gates/wave1-statements/evidence/S1210StatementsProbe.lean.txt`):
- `POracle_eq_P_of_mem_P`, which rests on W2-S alone;
- `NPOracle_EXPCOM_subset_EXP`, the summit;
- `baker_gill_solovay`.

Each is `rfl`-identical to its campaign statement, as are the three `EXPCOM` identities the
probe also derives. The probe's deterministic inclusion `POracle_EXPCOM_subset_EXP'` is
probe-local: it is derived from W2-S directly and has no campaign counterpart.

B5's own `exists_EXPCOM_decider` (home `Diagonalization/EXPCOM.lean`) is the summit's
query dispatcher. It is a B5 obligation, not a §12.10 row.

### 12.11 The format-parameterized code simulator (B5a; statements landed 2026-10-11; headline H1 by user decision, H2 in the backlog)

**Why.** Plan §4e decision 2: "B5 builds one format-parameterized uniform interpreter and
discharges ZF-B4, on top of 12.2c item 8's parameterized parse layer".
- `Universal`'s interpreter is hard-wired to one work tape, and is already copied once inside
  `Universal.lean`.
- ZF-B3's layer in `Codes2Tape` is format-specific and contains no interpreter.
- `CodeFormat` has no machine semantics.
- The two target files cannot host a layer for each other: EXPCOM's closure contains neither
  CounterLoop nor VirtualInput, and Codes2Tape is not imported by EXPCOM.

Hence a pre-issue statement module.

**Rows** (`TuringMachine/CodeSimulator.lean`).
- **`Turing.MachineFormat extends CodeFormat`** adds:
  - a work-tape count `k`;
  - a semantics `machine`;
  - two laws: `serialize_eq`, the fixed `k`-record serialization `serializeK`, and
    `skipTable_eq`, the fixed skipper `codeSkipTableK k`.
- **The generic writer layer:** `workReadsK`, `tableBitsK`, `serializeK`, `codeSkipTableK`,
  with proved bridges `tableBitsK_two` and `codeSkipTable2_eq_codeSkipTableK` to the frozen
  two-tape writers.
- **`oneTapeMachineFormat`,** public and proved. Its `decode` is `codeDecode`, and its
  machine is `CodeTM.toFinTM`, both by `rfl`.
- **`MachineFormat.exists_polyCanonizer`** (sorried): one machine computing
  `F.serialize (F.decode α)` in polynomial time. It serves the simulator's front end, the
  `canonizer` field of both uniform schemes, and, off-batch, the TMSAT concrete-scheme
  canonizer.
- **`MachineFormat.exists_uniformSimulator`** (sorried), **H1**. On
  `⟨⟨bits t, α⟩, x⟩` it answers `[true]` iff the decoded machine computes `[true]` on `x`
  within `t` steps, and `[false]` otherwise, within `d·(|α| + |x| + t + 1)^d`. This is
  field-for-field the shape of `UniformMachineCode.simulator_accepts`/`_rejects` and their
  `…2` mirrors.

**Inside H1:** exactly one private interpreter trace, a step block for one simulated
transition of a `k`-tape coded table. It is hosted by §12.7's `counterLoopTM` and Z1's
`vhostEmitTM`, built from the §12 layer, and is not a copy of `universalInterpreter`. Its
properties:
- states independent of the code;
- per-round cost `c·(|β| + 1)`, independent of `t` and `x`;
- input read only through its own head;
- silent;
- proved at the relation level.

Per-round cost independent of `t` and `x` lets stage 1, B6 and the NTIME deterministic core
reuse it under different hosts.

**Instances** (B5a fill):
- **EXPCOM:** `exists_uniformMachineCode` at `oneTapeMachineFormat`.
- **ZF-B4:** `exists_uniformMachineCode2` at a private two-tape format in `Codes2Tape`, whose
  laws are the two bridges.

The two assemblies are a forced mirror pair, as their target structures are. Both are
assembled from H1 in `campaign/gates/wave1-statements/evidence/B5aStatementsProbe.lean.txt`, resting only on the
two contracts. **NDCodes is not an instance:** ND codes denote NDTMs and need no interpreter.
A separate small parse-layer rider can handle them.

**Decisions** (from the dossier's D1–D9):
- **D1 (user, 2026-10-11).** A pre-issue statement phase. It is landed by the combined
  statement PR, under one gate.
- **D3 (user, 2026-10-11).** Headline **H1** for now. **H2** is per-code linear,
  `d·(|α|+1)^d·(t+1)` with no `|x|` term. It would serve stage 1 directly, but forces
  in-place suffix input and a suffix-input host that does not exist. H2 is recorded in
  `backlog.md`, and its corollary to H1 is proved in the probe.
- **D2 and D4–D9 are fill-brief matters**, settled when the B5a brief issues. The dossier
  recommends route Z, the generic interpreter at `k = 1`, for EXPCOM, with route W
  (Universal plus a post-processor) as an escalation fallback only. It also recommends moving
  ZF-B3's semantic layer into `CodeSimulator`, generalized, and deleting the dead ZF-B3
  privates.

**Forced writer pairs.** The generic `tableBitsK` reproduces part of the frozen writers'
text. The statement screen gives three such pairs: `oneTapeFormat` at 85%, `codeTable2Bits`
at 67% and `Code2TM.serialize` at 56%. The frozen bodies cannot be redefined, and
`tableBitsK_two` proves the equalities. This is item 8's pre-named residual watch item.

## 13. The zone and virtual-input layer (proposed 2026-10-09, post-§12 close)

**Mandate** (user direction 2026-10-09, at the §12 fill-campaign close —
track A of the two parallel tracks, the other being the chapter-1/2
retrofit): the §12 scope note **R9 promoted**. R9 drew the line at
physical-tape selection — `ι` relocates whole tapes and "the Hennie-Stearns
and universal-machine consumers get their zone/virtual-input representation
layers separately" (`Build/Embed.lean` header). This increment is that
separate layer. It gates the two stage-1 builds (the Hennie-Stearns `k`→2
conversion and the two-work-tape universal machine, plan §2.1/§4b) and is
scoped, like §12, beyond its first consumers: the virtual-input half serves
the `NP^EXPCOM ⊆ EXP` summit and the 12.2c dedup, and the zone half is
shaped so the chapter-1 Robustness conversions can gain **space theorems
additively** (plan §2.7's fallback route to Ex 4.1/Thm 4.8). §12's space
mandate continues: **every item carries a space clause alongside its time
cost** (`Turing.MultiTapeTM.spaceUsed`, work tapes only).

**Evidence.** The virtual-input pattern has now been hand-built four times
over the proved corpus: the A2 forwarding controller's
`a2_mapVirtual`/`a2_mapVirtual_step`/`a2_mapVirtual_run` lockstep (15 of
its 45 privates; both boundary clamps, empty-word case, halt absorption —
all proved), F2A's `f2_splitCountAction`/`f2_splitCount_run`
(virtual *empty* input over preinstalled banks), the universal
interpreter's prefix-input discipline, and the oblivious candidate's
`obliviousVisit` virtual-tape transduction. All four sit on the same public
primitive — `virtualMove`/`VirtualTag`/`virtualNextTag` and
`bufferTape_inputSymbol` (`Simulation.lean`) — and each rebuilt the hosting
and lockstep privately. On the zone side, the in-repo precedents are the
`SingleTape.lean` multiplexing encoding (`SweepCell`/`tapeRow`) and
`ObliviousSetup.lean`'s guide-zone layout with its two-directional run
identities; what does not exist anywhere is a *reusable* zoned carrier with
shift routines. The F2 epoch audit's three optional regression corollaries
(zero-time startup, both virtual-input clamps, setup followed by an
emitting halting step) are adopted here as permanent lemmas of Z1.

**What already exists and is consumed, not duplicated**: the §12 layer
itself (R1/R2 and the catalog rows are the assembly language of every
construction below); `virtualMove`/`VirtualTag` (`Simulation.lean`);
`Turing.actionBits₂` and the `CodeNDTM` two-work-tape serialization
(`NDCodes.lean`, statement-frozen under the closed P3.3 gate) — Z3 builds
the deterministic sibling against the same record format, never a second
serialization; `UnaryTape.lean`; the harvest policy of §8 (reimplement
against the ABI with the original proof as template; audited originals stay
in place until the separately-tracked retrofit/12.2c dedup).

### Z1. Virtual-input hosting (the `a2_mapVirtual` pattern, promoted)

A transformer hosting a machine whose input is a **designated buffered
word** rather than the native input: given a host with an injective tape
selection (R1's `ι`) plus one buffer tape holding `y`, the hosted machine
runs with `y` as its virtual input, buffer head at
`source.inputPos - 1` under a `VirtualTag` boundary discipline. Spec shape:

* **lockstep** — one host step per source step, transported `runFrom`
  identity (the A2 `a2_mapVirtual_run` shape, generalized from its
  two-buffer controller to the R1 selection);
* **clamps** — both boundary clamps hold with **no nonempty-`y` premise**
  (empty `y`: position `0` is the right boundary, `-1` the left; outward
  moves stay, inward moves cross) — the binding A2/F2 audit contract;
* **halt absorption** — the source's halting action executes before the
  host control dies; later times are fixed;
* **emission policy** — suppressed or forwarded, mirroring R1's two modes
  (open decision 12.4 resolves both at once);
* **time** — exact; **space** — coefficient-one containment: each selected
  tape's host visited set is contained in the source's visited set on `y`
  at the same horizon (the R4 ledger shape, proved in `a2_map_space`).

Permanent regression lemmas (audit-adopted): the zero-time startup
instance, the two empty-`y` clamp instances, and the setup-then-emitting-
halt seam. Generic form of: `a2_mapVirtual*` (A2), `f2_splitCount*` (F2A,
the `y = []` specialization), the universal interpreter's input phase, and
the query simulation every oracle-summit machine will need.

**Z1 rider — the R1 selected-tape exports (decision D-R1, user
2026-10-09, from the retrofit inventories, plan §4d).** The three retrofit
inventories independently identified the same R1 API gap: `Embed.lean`
exports no selected-tape field lemmas (`embedSlot_selected`/`_unselected`
are private) and no agreeing-host lockstep, so no old-code R1 consumer can
be proved from the public surface. This statement phase adds, **additively
in `Embed.lean`** (shared-file mechanism, audited under this gate): public
selected-tape projections of `embedSilentCfg`/`embedEmitCfg` (contents and
head of tape `ι i`), and an `ofWords` transport form. Unlocks the blocked
Hardness families (M/N/AM/U, Z/AB/AG — ≈ 300-350 lines) at the next
retrofit window.

### Z5. Machine-agreement transfer (decision D-R3, user 2026-10-09)

A general lockstep-transfer lemma, the `hagree` genre of
`capture_run`/`emit_run` made standalone: two machines over the same tape
count and state type whose transition tables **agree on a set of states**
run identically, configuration for configuration, from agreeing starts for
as long as the run stays inside the agreement set; a guarded variant takes
the agreement hypothesis per reachable state. Natural home:
`Simulation.lean` beside the existing lockstep gadgets (placement open
decision 13.5: Simulation versus a `Build/` module). Customers (rule of
admission): the Loop forwarding host (H3's 14 verbatim re-proved phase
lemmas, ≈ 550 lines, collapse to one transfer — `emLoopHost` agrees with
`loopHost` on every non-body state); the 13 guarded `clSlot_run` agreement
sites in `CookLevin/Hardness.lean`; every future mode-variant host (the
§12 loop hosts' decision/find/emit triplet is exactly this pattern).
Estimate: ≈ 4 points spec + fill; the risk is quantifier placement on the
agreement set, not proof content.

### Z2. Zoned tape carrier (the Hennie-Stearns representation)

The representation of `m` virtual work tapes on **one** physical tape with
amortizable locality: a `ZoneLayout` (level count `ℓ`; per-level zones
`L_i`/`R_i` of capacity `2^i` around a home origin, [AB09] §1.7) and a
carrier predicate `ZoneCfg` relating one physical word to `m` virtual words
plus per-zone fullness states (empty / half / full). The layer owns:

* **the carrier** — `ZoneCfg` well-formedness, read/write-at-home
  contracts (the virtual heads always sit at the physical origin), and the
  cell-encoding convention (open decision 13.2: how `Option Bool` virtual
  cells embed into binary physical cells — paired-cell presence/data
  tracks, with `SingleTape.lean`'s `SweepCell` encoding as the precedent);
* **the shift routines** — per-level `shiftIn`/`shiftOut` rebalancing
  rows with **exact** costs `O(2^i)`, assembled from R3
  transfer/copy/clear via R2 seams, each with its space row (visited cells
  within the touched zones);
* **the cardinality lemmas** — visited-set bookkeeping for multiplexed
  tapes: physical space bounded by the sum of touched zone extents, the
  piece the Robustness space annotation (Z4) consumes.

Explicitly **on top, not inside**: the `2^i`-fullness invariant across a
run, the amortized `O(T log T)` charge, and the simulation theorem itself —
those are the Hennie-Stearns consumer's mathematics (plan §2.1), as the
§12 precedent kept the loop ledgers out of the loop host. Scope note:
Z2 is sized for the H-S discipline (one zoned tape + one scratch tape);
a general `k`→`k'` conversion is not in scope.

### Z3. Two-work-tape codes (the deterministic `actionBits₂` sibling)

The deterministic code layer currently covers only the one-work-tape
binary normal form (`EffectiveMachineCode`/`UniformMachineCode`,
`Encoding.lean`), which is why Thm 3.1 arrives at `f²` (plan §2.1). Z3
extends it: a deterministic two-work-tape code scheme over the
**same `actionBits₂` record format** as `CodeNDTM` (one branch instead of
two), with the `CodeParser` extension and the `UniformMachineCode`-style
uniform-decoding clause (the P3.2 lesson: variable-code consumers need the
uniformly-timed form). The two-work-tape **universal machine itself** is
the stage-1 consumer build, not part of this layer; Z3 ships the codes it
reads. Space rows on the parser rows from the start.

### Z4. Space annotation for the Robustness conversions (consumer-driven)

Additive `spaceUsed` theorems for the chapter-1 conversions
(`one_work_tape`, the alphabet reduction) via Z2's cardinality lemmas — no
signature changes, the audited surface untouched (the R3 retro-annotation
precedent). This is plan §2.7's fallback route to the space-efficient
universal (Ex 4.1, Thm 4.8). **Design-time obligation, recorded here**: at
the Z1-Z3 spec phase, assess whether the two-work-tape universal carrying
Z1/Z2 space rows yields Ex 4.1 directly; the answer (and hence whether Z4
is needed at all, and at which strength) is recorded before the statement
gate, so the chapter-4 risk register (§6 summit 1) is settled either way.

### Consumers (rule-of-admission check, §4: two named customers per item)

| Item | Customers |
|---|---|
| Z1 virtual-input hosting | the two-work-tape universal (stage 1); the `NP^EXPCOM ⊆ EXP` summit's query simulation; the 12.2c dedup of `a2_mapVirtual*`/`f2_splitCount*`; the P3.3 universal-NDTM fill's code/input discipline |
| Z2 zoned carrier + shifts | the Hennie-Stearns `k`→2 conversion (plan §2.1); the Robustness space annotation (Z4); the Ex 1.6 oblivious sharpening (recorded stretch goal, `Robustness/Oblivious.lean`) |
| Z3 two-work-tape codes | the two-work-tape universal; the Thm 3.1 re-derivation at `f log f` (Hydroxyi's diagonal argument over the new codes) |
| Z4 space annotation | Thm 4.8/Ex 4.1 fallback (plan §2.7); `L ⊊ PSPACE`/space-hierarchy fills (P4.3) if the universal route stalls |

### Placement, sequencing, cost

* New files `Build/VirtualInput.lean` (Z1) and `Build/Zone.lean` (Z2),
  namespace `Turing.FinTM`, order list after `Build/Catalog`; Z3 as a new
  `TuringMachine/Codes2.lean` beside `Encoding.lean` (placement open
  decision 13.3: a new file versus extending `Encoding.lean` — the frozen
  audited surface of `Encoding.lean` argues for the new file); Z4 lands
  additively in the `Robustness/` files through the shared-file mechanism,
  flagged for its own audit.
* Process per `workflow.md`, the §12 precedent verbatim: maintainer-serial
  spec layer (quantifier-sensitive), statement gate by external audit,
  fills as briefed batches with exclusive ownership, epoch-boundary fill
  audit. The gate must close before the H-S/two-tape-universal builds
  start; chapter-3/4 fill briefs written while this layer is open simply
  do not cite it (the EXPCOM brief prefers Z1 only if Z1 is closed).
* Estimate (campaign points): Z1 ≈ 8 (harvest-grade — the lockstep is
  proved four times over; the risk is quantifier hygiene, not proof
  content), Z2 ≈ 14 (genuinely new; the carrier predicate is the risk
  concentration, L-style), Z3 ≈ 6 (format fixed by `actionBits₂`), Z4 ≈ 6
  (retro-annotation against Z2's lemmas). Total ≈ 34, between the §12
  statement layer and one fill epoch.
* **Citation duty** (binding, the 2026-10-06 guideline and the 2026-10-08
  citation-audit row): the design adapts [AB09] §1.7 (Hennie-Stearns) and
  Exercise 1.5/1.6; the §12 duty extends here — Édouard Bonnet's
  lax-434930 `classical-complexity` (Apache-2.0, commit `0c084031…`) is
  cited in this addendum, the module docstrings, and the blueprint entries
  wherever its stack-machine routine catalog informed a row's shape; no
  external code is imported or transcribed.

### Open decisions (13.x, for the user at spec time)

1. **13.1 Zone discipline**: zones-with-fullness (the [AB09] §1.7 layout,
   proposed) versus plain interleaving (simpler carrier, no amortized
   locality — insufficient for H-S alone, but cheaper if Z2's only
   customer were Z4). Proposed: zones; interleaving is not built.
2. **13.2 Cell encoding**: how `Option Bool` virtual cells embed in binary
   physical cells (paired presence/data cells proposed; `SweepCell` as
   precedent).
3. **13.3 Z3 placement**: new `Codes2.lean` (proposed) versus extending
   the frozen `Encoding.lean`.
4. **13.4 Z1 mode shape**: one transformer with an emission-mode parameter
   versus two transformers — inherits open decision 12.4's resolution.
5. **13.5 Z5 placement**: the agreement-transfer lemma in `Simulation.lean`
   beside the lockstep gadgets (proposed) versus a `Build/` module.


### 13a. Decisions resolved; epoch structure (user, 2026-10-09)

All five open decisions resolved as proposed, with one rename:
**13.1** zones-with-fullness (interleaving is not built); **13.2** paired
presence/data cells (`SweepCell` precedent); **13.3** a new file, renamed
**`TuringMachine/Codes2Tape.lean`** so the "2" reads as *two-tape*;
**13.4** Z1 inherits 12.4's resolution (a silent/emit transformer pair over
one shared core); **13.5** Z5 lands in `Simulation.lean`.

**The statement phase runs in two tranches, each with its own gate:**

* **A-S1 — the virtual-input half**: Z5 (the agreement transfer,
  `Simulation.lean`, additive), Z1 (`Build/VirtualInput.lean`, new), and
  the Z1 rider (the R1 selected-tape exports, `Embed.lean`, additive via
  the shared-file mechanism). Rationale: harvest-grade risk (the lockstep
  is proved four times over; the rider's facts are proved privately), and
  its consumers are the *near-term* ones — the blocked retrofit R1
  families, the 12.2c dedup, the Loop H3 collapse, the EXPCOM summit.
* **A-S2 — the zone half**: Z2 (`Build/Zone.lean`), Z3
  (`Codes2Tape.lean`), Z4 (the Robustness space annotation). Rationale:
  Z2's carrier predicate is the genuine design risk and deserves an
  undiluted gate; its consumers (Hennie-Stearns, the two-tape universal)
  sit one stage later. The Z4 design-time obligation (does the two-tape
  universal's space bonus yield Ex 4.1?) is discharged in the A-S2 pack.

The canonical Z1 shape (spec-time refinement, recorded before drafting):
the transformer is defined on exactly `1 + M.k` work tapes — the buffer
first, the payload bank after it — and **relocation is not baked in**:
a consumer needing the buffer or bank elsewhere composes with R1. One
shared hosting core; `silent`/`emit` flavors per 12.4; the tag lives in
the transported control state (the `a2_MapState.run q tag` precedent).

### 13b. A-S1 gate close (2026-10-09, after `campaign/gates/vhost-infra/findings.md`)

Round-1 **PASS, 0 blockers / 0 majors / 2 minors**; loop summary
`campaign/gates/vhost-infra/resolutions.md`. Minor sweep recorded here per the
audit's proposed fix (A-S1-2): the Z1 rider's promised **`ofWords`
transport form is supplied by specialization** of the four delivered
selected-tape projections (instantiate `c := Cfg.ofWords …`); no
separately named specialization is exported now — if a consumer wants the
whole-configuration identity (with its frame, capture, head, and output
parameters spelled out), it is commissioned on need at the 12.2c window.
A-S1-1 (the pack under-counted the definitions: eight with
`MultiTapeTM.AgreeOn`, 23 audited declarations) is acknowledged as a pack
erratum; shipped packs stay verbatim. The audit's four recommended sanity
exports (initial-tag validity + `q₀`-independence, fixed-parameter
transport injectivity, native-head constancy for arbitrary host
configurations, named boundary/seam specializations) are **adopted as
optional permanent lemmas of the A-S1 fill brief** — offered, not
required. The audit's Z5 composition-of-responsibilities reading is
affirmed and binding on retrofit consumers: Z5 equates runs on one
carrier; heterogeneous `clSlot_run`-style sites first transport
(R1 + state renaming), then agree — a public guarded
configuration-transport theorem is a possible later export, not promised.

### 13c. A-S2 round-1 repairs (2026-10-09, after `campaign/gates/zone-infra/findings.md`)

The A-S2 statement gate returned **FAIL: 1 blocker, 1 major, 2 minors**;
repairs landed with the round-2 pack:

* **A-S2-1 (blocker) → the inward room premise removed and the wrappers
  split.** The spec had one shared room hypothesis on both shift
  directions; inward shifts *remove* donor cells, so a full donor — the
  exact classical case — was illegal, and the audit's full-chain family
  showed the delivered interface forcing `Ω(T²)` behavior. Repair:
  `zoneShiftInW` carries no room condition; `zoneShiftOutW`'s receiving
  room moved **inside its guard**; the contents wrappers are the
  hypothesis-free `zoneShiftIn`/`zoneShiftOut`; the head steps gain the
  guarded-total `zoneMove`; and the audit's required gate material landed —
  the full-donor regression (`zoneShiftInW_full_donor`) and the cascade
  statements (`zoneCascadeRight` with its represented-word, length, and
  geometric-cost lemmas), whose proofs adopt the audit's schedule analysis
  as the binding route. The rows now realize the **total guarded
  operation, identity branch included**.
* **A-S2-2 (major) → the Z4 one-tape sketch replaced.** The received
  `sweepTM` grows its window unconditionally (the audit's stationary-head
  scanner refutes it as a witness); the statement stands, and the binding
  route is now a **demand-grown** sweep witness with the audit's
  union-of-origin-intervals bound, interleaving factor, and the
  all-`Γ'`-inputs retraction (empty-alphabet and zero-tape cases named).
* **A-S2-5 (note, adopted) → the Ex 4.1 assessment stands as a
  *design-level* verdict, not an implementation discharge**: the stage-1
  universal must specify a space-accounted input interface (native/suffix
  access or an accounted buffer — a materialized input copy costs
  `Ω(|x|)` work cells, absent from the sketched ledger) and a parser with
  its own space ledger; the uniform scheme (Z3), not an arbitrary
  effective scheme, is what a space-accounted canonizer route would use.
* Minors: the pack's definition count corrected (22, not 25; inventory in
  the findings); the module's export list and the guard semantics
  docstrings corrected in place (A-S2-4).

### 13d. Revision: the zone layer at the book's design (draft, 2026-10-10)

**Status: design draft for user review. No Lean change has been made.**

**Process rule (user, 2026-10-10, binding for this revision).** Every Lean change
that results from this revision goes through **both** human approval, as a PR
the user merges, **and** a separate audit gate. Nothing is pushed directly to
the campaign branch. This covers the library generalization (G1), every new
statement phase, and every fill.

#### Why

ZF-A3 (`zone-f1-A3.zip`, held and not integrated) proved infrastructure only:
a geometric counter schedule, counter-driven navigation, a counter built from
the unary level, a window readout, and counter removal, 952 lines in all.
Neither shift machine was proved. A comparison with [AB09] §1.7 traces the
cost to four of our choices, not to the mathematics:

1. **A supplied level with pairwise shifts.** Each pairwise shift starts from
   home, so the machine must count its way to level `i`. In [AB09] the index
   `i₀` is *discovered* by scanning outward, and one sweep does all the work
   between adjacent zones where the head already is.
2. **No markers.** A binary physical tape carries no zone boundaries, which
   forces the binary counter.
3. **Catalog reuse on packed zones.** The generic routines need a blank on
   each side of a word, but packed zones abut, hence the save, blank, call,
   restore cycle around every call.
4. **Exactly two tapes per row,** so the counter shares the scratch tape with
   the level word.

There is also a **gap independent of the controller**. Plan §2.1 specifies
the book's route ("parallel tracks, buffer zones of size `2^i`, amortized
shifts"), but `ZoneContents` holds **one** simulated tape, and both rows
operate on a tape dedicated to it. In a two-tape simulator only one tape can
be zoned, so the present carrier serves only machines with one work tape,
and Hennie–Stearns needs each of `k` tracks to shift independently.

#### Decisions taken (user, 2026-10-10)

- **A rich alphabet, finished by alphabet reduction.** The Hennie–Stearns
  simulator is a two-tape `FinTM Γ` over a large alphabet `Γ`, as in [AB09]
  via Claim 1.5, and the public `Turing.FinTM.alphabet_reduction`
  (`Robustness/AlphabetReduction.lean`) finishes it. That theorem preserves
  the work-tape count (`M'.k = M.k`), costs `3(|Γ|+1) + 2` steps per source
  step, and is stated at the function level (`ComputesFunInTimeVia e f T`
  gives `ComputesFunInTime f (c·(T+1))`). A space form exists
  (`alphabet_reduction_spaceUsed`).
- **Option (b): generalize the library to arbitrary alphabets** rather than
  building a parallel `Γ`-only toolkit. Large-alphabet machines will recur.

#### Components

**G1. Alphabet-generic library (in place).** Change `Bool` to an arbitrary
`{Symbol : Type*}`, with `DecidableEq` where needed, in:

- **`Build/Seam.lean`:** `seamCompTM`, `seamReleaseTM`, and their
  general-configuration theorems (the `_ofCfg` trio and the release pair).
  The canonical `Cfg.ofWords` theorems stay Bool-specific and become
  instances of the general ones.
- **`Build/Embed.lean`:** the transformers, transports and all their
  theorems, including the RB5 state-transport lemma. The capture tape's
  buffer generalizes with `bufferTape`.
- **`FinTM.bufferTape`** (`Simulation.lean`): from `List Bool` to
  `List Symbol`. The definition is unchanged.
- **The R3 sweep rows in `Build/Catalog.lean`:** `transferTM`, `copyTM`,
  `clearTM`, `compareTM`, and their §12.6 framed contracts. Their tables
  never inspect a symbol's value except for equality, so they generalize.
  `incrementTM`, the canonical rows and the Part 2 space rows stay
  Bool-specific.

**Binding constraint:** every existing Bool statement either keeps its
statement verbatim or becomes a definitional instance at `Symbol := Bool`
that its consumers elaborate unchanged. The full downstream replay is the
evidence. This is a change of audited public signatures, so it gets **its
own gate**, before anything consumes it.

**G2. Mapped sweeps (new, alphabet-generic catalog rows).** Per-track
shifting moves one *component* of each cell and leaves the other tracks in
place, which whole-symbol copying cannot do. The rows are `copyMapTM` and
`transferMapTM`, parameterized by `extract : Γ → Δ` and
`merge : Γ → Δ → Γ`: they write `merge (dst cell) (extract src cell)`. Their
framed contracts follow the §12.6 shape (exact time `2|w| + 2`, finish
configuration, no earlier exit, trajectory). At `merge := fun _ s => s` they
are the plain rows. This is the reusable large-alphabet primitive. Its proofs
must share the generalized R3 trace, not copy it (one trace per routine
family, as §12.6 established). **Decision (user, 2026-10-11; the §12.8
statement gate's Q7).** G2's one-tape core is `scanTM` (§12.8a).
`copyMapTM`/`transferMapTM` stay, for the cross-tape G3/G4 consumers. Their
`merge` takes `Option Γ → Δ → Γ`, so that blank destinations are admitted,
and they share one trace with the scan.

**G3. The multi-track zoned carrier over `Γ`.**

- **Alphabet:** `ZoneSym k := Bool ⊕ ZoneCell k`, where
  `ZoneCell k := Fin k → Option (Option Bool)`. Per track, `none` is the
  buffer symbol `⊠` (an unoccupied slot) and `some v` an occupied slot
  storing the virtual symbol `v`. `Sum.inl` embeds the binary input and
  output (the `e` of `ComputesFunInTimeVia`). It is finite, so it is a
  `Fintype`.
- **Contents:** `Fin k → ZoneContents ℓ`. **The pure layer is reused
  verbatim per track:** the codec is unneeded, but the layout arithmetic,
  `ZoneContents`, `zoneSlot`, `zoneSide`, the pairwise ops and their
  word-preservation lemmas, the head steps, and the cascade with its
  lemmas all carry over.
- **Layout:** one physical cell per virtual slot, holding the whole tuple,
  with the home at cell 0 and **one blank separator cell between consecutive
  zones** on each side (decision 13d.1). Each zone is then a blank-delimited
  nonblank word of length `zoneCapacity i`, so the generalized framed sweeps
  (G1, G2) apply directly, with **no save/restore**. The separators also mark
  zone boundaries, so **no counter** is needed.
- **The home cell** holds all `k` tracks' virtual symbols, so the simulator
  reads and writes the virtual heads in one step.

**G4. Rebalance rows.** For a direction `d` and a track `t` (`t` in finite
control, since `k` is fixed for a given simulated machine), one machine:

1. starts at home and **scans outward** across zones, using the separators,
   to find `i₀ := zoneShiftIndex d (z t)`, the least level whose zone on the
   feeding side is non-empty. This is a new pure definition;
2. realizes the pure cascade at `i₀` on track `t` in a single
   outward-then-inward sweep, with mapped sweeps between adjacent zones and
   the scratch tape as the buffer;
3. leaves every other track and the separators unchanged, and returns home.

Its contract has the same shape as the current rows: exact final tape, live
exit or halt as the consumer needs, time `O(2^{i₀})`, the head within the
level-`(i₀+1)` extent, and scratch space `O(2^{i₀})`.

- **The left-move mirror** `zoneCascadeLeft` is new. It is defined through a
  pure left/right swap of `ZoneContents`, with its lemmas derived by
  symmetry, never copied.
- **The extent:** the carrier lays out `ℓ` levels, and a separate
  **extension row** lays out level `ℓ` (separator plus a half-full fresh
  zone, as in [AB09]'s "first time we encounter it") in `O(2^ℓ)`
  (decision 13d.2).

**G5. The assembly (stage-1 consumer, sketched for fit, not part of this
layer).** One simulated step:

1. read the home tuple;
2. apply M's transition in finite control;
3. write the home tuple;
4. rebalance each track by its head's move: `k` calls of G4, plus extension
   when needed;
5. handle the input and output tapes directly.

The amortization `Σ_i T/2^{i-1} · 2^i = O(T log T)` is the consumer's
mathematics, as before. Then `alphabet_reduction` turns the two-tape
`ZoneSym k` machine into a two-tape binary machine. With the Z3 two-tape
codes and the two-tape universal machine, Thm 3.1 follows at `f log f`.

#### What stays and what goes

- **Kept unchanged:**
  - the pure zone layer in `Build/Zone.lean` (about 820 of its 1,191
    lines): layout arithmetic, carrier, represented word, pairwise ops, head
    steps, the cascade and its lemmas, and the cardinality export. Its
    statements are untouched;
  - the rest of §13: Z1, Z3, Z5;
  - §12.6 and §12.7.

  No other file imports `Zone.lean`.
- **Superseded, to be retired through the G3/G4 gate:**
  - the binary physical realization `zoneTape`, `zoneTape_empty`,
    `zoneTape_blank_outside` and `zoneTape_homeWrite`;
  - the paired-cell codec, unneeded with a rich alphabet;
  - ZF-A2's seven staging-window lemmas;
  - the two current row statements, `exists_zoneShiftInTM` and
    `exists_zoneShiftOutTM`, to be replaced by the G4 rows.
- **ZF-A3's checkpoint** is held, not integrated. Almost all of it (counter
  navigation, counter construction, the binary window readout) becomes
  unnecessary. Integrate nothing from it unless G4's design reuses a piece.

#### Sequencing (each Lean step a PR plus its own gate, per the rule above)

1. **G1:** the generalization as one batch, its statements verified as
   instances, with the full downstream replay; then a **G1 audit gate**.
2. **G2–G4 statements:** the mapped sweeps, the carrier, the rebalance and
   extension rows, the swap mirror and the index function, with an executed
   pre-ship check on concrete instances; then a **statement gate**.
3. **Fill batches** for G2 and G4, then a **fill gate**.
4. The stage-1 Hennie–Stearns assembly, which needs its own statement
   phase.

#### Open decisions (13d.x, for the user)

1. **Zone boundaries:** blank separator cells (proposed; they give the
   catalog delimiters and boundaries at once) or a boundary flag in `Γ`
   (needs predicate-stopping sweeps instead).
2. **The extent:** a laid-out `ℓ` plus an extension row (proposed), or
   rows that extend lazily themselves.
3. **Rebalance totality:** realize the total pure cascade at the scanned
   index for every input (proposed; the A-S2 totality lesson, and the pure
   ops are already total), or a contract conditional on the classical
   fullness invariant.
4. **The track index:** in finite control, one row instance per
   `(direction, track)` (proposed), or on a tape.
5. **The shape of `Γ`:** `Bool ⊕ ZoneCell k` (proposed) or a structure
   with a bit field.
6. **Retiring the superseded declarations:** delete them through the G3/G4
   gate (proposed, since nothing imports them), or deprecate them first.
7. **G1's extent:** whether `Build/Loop.lean`'s public hosts also
   generalize now, or only when a large-alphabet consumer needs them.
   Proposed: only Seam, Embed, `bufferTape` and the R3 sweeps now.

#### Decisions 13d.1–13d.7 taken (user, 2026-10-10): all as proposed

1. Zone boundaries are **blank separator cells**.
2. **A laid-out `ℓ` plus an extension row.**
3. **Total rebalance contracts**: the rows realize the total pure cascade at
   the scanned index for every input.
4. **The track index lives in finite control.**
5. **`ZoneSym k := Bool ⊕ ZoneCell k`.**
6. The superseded declarations are **deleted through the G3/G4 gate**.
7. **G1 covers only Seam, Embed, `bufferTape` and the R3 sweeps.** What this
   means for the sweeps: the *definitions* of `transferTM`, `copyTM`,
   `clearTM` and `compareTM` (the last needs `[DecidableEq Symbol]`), and the
   three framed sweep contracts `transferTM_run_ofCfg`, `copyTM_run_ofCfg`
   and `clearTM_run_ofCfg`, generalize. The canonical `Cfg.ofWords` rows,
   the space rows, the compare contracts, and everything about `incrementTM`
   stay Bool-specific. The generalized definitions instantiate at `Bool`.

The G1 brief is `campaign/fills/s13d/briefs/s13d-g1-generalize.md`.

**Scope (user, 2026-10-12; §16b item 5).** G2–G4 and the Hennie–Stearns assembly stay in this
campaign. They follow MIG-0b, so that their rows are stated as `Contract`s from the start.

## 14. Hosts first: the rule and the host registry (user, 2026-10-12)

**The rule** (`policy.md` §1, **Hosts come first**; `workflow.md` §2 and §4,
ground rule 4). A *host* is a control structure that drives other routines:
a search or traversal, a recursion or evaluation scheme, an interpreter step
block, a clocked or windowed runner, a dispatcher over a data structure, or an
input device. A host is never built `private` inside the proof that first
needs it. Its public contract is designed and statement-gated first, generic
in what its consumers vary, with time and head-envelope clauses; consumers
cite it, proved modulo while its fill runs. Leaf rows (copy, compare, seek,
arithmetic) are not hosts and keep the §4 rule of admission.

**Why** (the library-reuse assessment of 2026-10-12, four read-only reviews of
the tip `3462c1b4`). The configuration-level calculus (§12–§13: framed sweeps,
`scanTM`, seams, the phase host, R1 embedding, symbol lifts, counter loops,
configuration records) is general: alphabet-generic, with exact time, framing
and head envelopes. Overfitting entered one level up, where every theorem got
its own private host, because the briefs' ground rule 1 made new helpers
private by default:
- NP ⊆ PSPACE's evaluation host (`SpaceComplexity/Inclusions.lean`, about 70
  privates), S1b's BFS and windowed pieces (private by `campaign/fills/ch34/briefs/ch34-s1b.md`,
  which lists three promotion candidates), B4 membership's assignment walker
  (private by `campaign/fills/ch34/briefs/ch34-b4-mem.md`), and Cook–Levin's machine-to-formula
  kit (private in `CookLevin/Hardness.lean`);
- four configuration encodings (`coreCode`, `cfgRecord`, B4a's bit rows,
  Cook–Levin's snapshot blocks) and three reachability notions (configuration
  reachability in `ConfigGraph`, `Complexity.GraphReach`, `Kruskal.Reach`),
  none linked to Mathlib's `Digraph`/`SimpleGraph`;
- about 300 `f2_` private copies in `Build/Catalog.lean`, there only to attach
  space bounds to rows exported as existentials (the §2 design rule, *named*
  machines with spec theorems, was not followed by those rows).

**The registry.** Status as of 2026-10-12. Rows H7–H13, and the reconciliations of H1, H3, H4
and H6, were added 2026-10-14 (the ARM fill gate, finding 5). Row H14 was added 2026-11-05
(gate 03l, ruling R-03l-1). H15 was registered 2026-11-06 PST for the Pass–shelat
rejection-loop statement gate (gate 08, G08-01). Each entry gets a public contract
and a statement gate before a second consumer is briefed.

| # | Host | Status | Named consumers |
|---|---|---|---|
| 0 | **Framed-contract structure**: machine, entry/exit states, precondition, endpoint as a function of the start configuration, time, no-earlier-exit cut, head envelope; sequencing, phase host, R1 embedding, lift and counter loop as structure-to-structure theorems, space derived | to design; **requirements revised by §16** (exact time and cut first-class) | every host below; removes the inline restatements of the delimited-word precondition |
| H1 | **AND/OR evaluator**: a depth-first odometer over a path word of per-depth records with node kinds (AND/OR), a pluggable leaf-verdict module with its own framed contract, short-circuit semantics as a pure function; space = path + leaf + O(1) | **reconciled 2026-10-14:** the machine form exists, received: `LogProg.TQBFARM` (H13e) proves `TQBF_mem_PSPACE` by a depth-first walk with the assignment as a stack register (accepted exception). The private pure core in `TQBF.lean`'s `b4m*` appendix is dead and is deleted by the payback PR (D6); MIG-22 is moot. The general AND/OR evaluator remains to be designed; its contract gate decides between this machine and §15's language. *(Was: the pure core private in B4 membership's partial; language first, user 2026-10-12.)* | `TQBF_mem_PSPACE` (served by H13e); Savitch (served by H13a for polynomial `S`; midpoint records as digits); NP ⊆ PSPACE (re-derivation); `ClassPSPACE/Games.lean`'s game values; backtracking in the §15 layer |
| H2 | **Step block**: one simulated transition of a `k`-tape coded table, relation-level, with per-round time `B·(\|table\| + 1)` and a head envelope | **the complete step block is proved, private, in B5a H1's continuation (fills-7):** `h1RoundTM k`, one finite machine per `k` whose control does not depend on the state count, with `h1Round_effect` (`0 < T ≤ 50·(\|table\| + 1)`, strict interior, silent, head envelope). **Promoted (2026-10-14, H2-M, PR #88):** public in `Build/StepBlock.lean` as `Turing.StepBlock.roundTM`, with `roundTM_effect`, under the round-2 names (backlog F7-1(a)). **H2-L, its loop form, landed (2026-10-14, PR #94):** `Build/StepBlockLoop.lean`, `Turing.StepBlock.loopTM`/`hostedLoopTM` with `loopTM_run`, `hostedLoopTM_run`, `hostedLoop_read` (H1 harvest gate, CLOSED). **H2-F, its forwarding (unclocked) loop form (2026-10-15; U2 statement gate CLOSED, PASS 0/0/2; PR #102):** `Build/StepBlockForward.lean`, `Turing.StepBlock.forwardLoopCfg` (defined) and `Turing.StepBlock.exists_forwardLoopTM` (**proved**, 2026-10-16, the H2-F fill, landed by PR #114: the round block released into a phase host with a forwarding leaf, per-step cost `T + 3` live and `T + 2` at a halt, `C = 3`): a macro-step `Turing.Lockstep` of any `k`-tape table through `forwardLoopCfg`, emissions forwarded, per-step cost `0 < cost ≤ 50·(\|tableBitsK\| + 1) + C`, and a per-head space ledger (mirrored heads within the source's visited cells, the two auxiliary heads within that bound); its own module so that the clocked form's consumers (`CodeSimulator`) do not depend on it (user, 2026-10-15) | H1 (`exists_uniformSimulator`); U-1; B6's self-application universal; H2-F: U2-U (`exists_selfUniversalK`), U2-E (`universalK`), B6's `U₀` at `k = 1`, U-1; C1 (unchanged, at `k = 3`, through the replay machine `NDTM.replayTM`); EXPCOM |
| H3 | **Windowed runner**: run a fixed machine on a windowed record, exiting on window exit, simulated halt, or a configuration-count clock | parts exist privately in S1b's partial (radius phase, records-to-runs bridge, the general-`S` count). S1b stopped (fills-6); B6's window route is the next consumer (adopted, §16b item 3). **B6's hosts landed (PR #92, 2026-10-14):** `Build/WindowRun` and `SpaceComplexity/WindowClock` state its public contracts, sorried for B6's fills. S1b's remaining private block is dead, and the payback PR deletes it. See H9 for the received configuration count | B6 (the window route; gated, `campaign/gates/13-b6-hosts-statements/findings.md`); Savitch and NL = coNL (served by H13a and H13b); S1b (stopped) |
| H4 | **Search over a graph presented by rows** (enumerate, equality, adjacency, start, target), visited table, BFS | **reconciled 2026-10-14:** built at ARM level for `NSPACE ⊆ DTIME(2^O(S))` (H12, received, accepted exception); MIG-19 is moot. The general search over row-presented graphs remains to be designed (H10's code languages are a row presentation). *(Was: not built; language first, MIG-19.)* | `NL ⊆ P` and `NSPACE ⊆ DTIME(2^O(S))` (served by H12); Immerman–Szelepcsényi counting (served by H13b); `PATH ∈ P`; §15 graph algorithms |
| H5 | **Input devices** behind one interface: native, buffered (Z1, exists), unary marker, binary position (from `exists_inputSeekTM`), computed input | partial | B6 / `space_universal`; U-1 and H2 (backlog); C1 |
| H6 | **Machine-to-formula kit**: closed-form variable indexing, snapshot-keyed local gates, ordered emission by `exists_emitLoopTM`, Tseitin on `Std.Sat.CNF ℕ` correct for every prefix assignment | pattern private in `CookLevin/Hardness.lean`; B4a's codec is non-uniform (its orderings range over index types depending on `n` and `s`, and its public statement is `∀ n s, ∃ …`). **B4a is restated in place over this kit's indexing** (user, 2026-10-12; §16b item 2) | TQBF hardness (served instead by H13f's route: the uniform tableau, Tseitin after the prefix); Cook–Levin deduplication; later machine-to-formula reductions. B4a's restatement (§16b item 2) has no consumer while RD-2's fills are held |
| H7 | **ARM compiler and its decision bridges** (Hydroxyi's `LogProg` tree, `SpaceComplexity/Machines/`): the register-tape compiler from an arbitrary seam (`compile_correct_from`), the space bridge `arm_space`, and the decision bridges at logarithmic width (`arm_decides`, `arm_decides_poly`) and at general width (`arm_decides_space`, `arm_decides_SPACE`, `arm_decides_pspace`, `_of_logspace`, `_val`); the loop and reachability kit (`GuardLe`, `ARMLoops`, `arm_reach`, `VWord`) | **received 2026-10-14 (`8c23f3bc`); public, ungated; first uses an accepted exception (decision 3).** `compile_correct_from` and the wide bridges are new; `arm_decides`, `arm_space` predate (chapter-6 campaign, `f70c57c2`). No time clause: ARM instructions are unary in register values, so time goes through H9 | `TQBF_mem_PSPACE` (H13e), `PSPACE_eq_NPSPACE` (H13a), the codec's deciders (H10), the PATH-hardness bit deciders (H13d), `searchLang_mem_PSPACE` (example); through H8/H9 every ND and time customer |
| H8 | **Nondeterministic ARM (NARM)**: `choose` instructions driven by a choice word, compiled to a `FinNDTM` by the `detPart` override; the space bridge `narm_space` and the class bridges `narm_decides_space`, `narm_decides`, `narm_decides_poly`, `narm_decides_npspace`; the termination layer `NTerm`/`NAcc`/`NSem` | **received 2026-10-14; public, ungated; accepted exception.** Supersedes for now §16b item 4's route (C2 as programs with coins; stage 2 paused). Its all-branch budget is per input: uniform over one input's branches, not over input lengths | `PATH_mem_NL` (H13c), `compl_mem_NSPACE` and through it `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq` (H13b) |
| H9 | **Memory ARM (MARM) and its time bridge**: a monotone Boolean memory tape (`mread`, `mset`, `mleft`, `mright`), compiled by the same `detPart` override; the configuration count `runFrom_count_eq` and the bridge `marm_dtime` into `DTIME` | **received 2026-10-14; public, ungated; accepted exception.** The count needs the monotone-write hypothesis `hwrite` and is valid along one run only | `NSPACE_subset_exp_dtime` (H12), hence `NL_subset_P`, `polyTimeReducible_of_mem_NL` |
| H10 | **Configuration codec and code deciders** (the fifth configuration encoding): `cfgWord`/`cfgCode` over the shared window `Turing.Cfg.InWindow` (`TuringMachine/Build/CfgRecord.lean`), the bound `cfgCode_lt`, injectivity up to `NDTM.coreSum`, the decoder; the four code languages and their `LOGSPACE` deciders; the chain bridge `mem_iff_codeChain` / `mem_of_codePath` | **received 2026-10-14; public, ungated; accepted exception.** The codec's own window predicate `InWin` was retired into `Turing.Cfg.InWindow` by the payback (D1; PR #101, landed 2026-10-15; its 28 restatements gated post-merge by the ARM gate's round 3). RD-2's `ConfigCodec` has no consumer (fills held) | H13a (Savitch), H13b (inductive counting, through H13a's decider bank), H13d (PATH hardness), H12 (`ExpBFS`), H13f (TQBF hardness's verifier and machine) |
| H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index (their answers `indicator_inputBitLang`/`indicator_inputLenLang`), the stride decoder `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance), the increment/decrement chain `arm_chain`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` were done in the payback (PR #101, landed 2026-10-15): `Codec/Engine`'s `decodeStride_loop` and `incChain`/`decChain` are instances of `boundedDecodeStride_loop` and `arm_chain` | every received ARM customer through its decider bank; `Codec/Engine` (its decoder and chains are instances); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
| H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius` directly, `ISCountGenCorrect` transitively) |
| H13 | **The customer machines**, each with its named consumers and its own reachability notion: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |
| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`); head envelopes `Clean.envelope` (a clean module's heads stay within `B \|arg\|` cells of the origin at every time), `host_call_envelope` (within `t` cells up to time `t` of a call) and `host_clean_envelope` (`host_clean` with the envelope `B \|arg\|` throughout the call), the coarse envelopes from the time bounds and the unit head moves of `Turing.MultiTapeTM.workTapePos_step_le` | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round; head-envelope clauses added 2026-11-06 (gate 03l round 2, finding 1).** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
| H15 | **Block-rejection string-function host:** `TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL`, in `TCSlib/Cryptography/Candidates/Concrete.lean`. Given a parameter-dependent decidable test `E`, a polynomial-time bit test on paired parameter/value words, and polynomial-time words `par`, `kw`, `bw`, `tw`, `c`, publishes an existential polynomial-time output `g`: rejection is `g z = []`; otherwise the value is read from `(g z).tail`, whose length is at most `(kw z).length`. Sizes and trial count are the supplied words' lengths; no `k ≤ B`, positivity or full-coin-length premise is imposed. Depends on `Complexity.polyTimeComputable_iterateFind` (the repetition host in `Randomized/Repetition.lean`, via `Build/IterateFind.lean` and the H14 clean-module host). This layer exposes polynomial time and the payload-length bound; a separate machine head-envelope clause is not exposed. | **Statement only**, in PR #227; **gate 08 CLOSED**, round 2 PASS (0 blockers/0 majors/0 minors), audited head `84f35910912bd3d1cd520beea9469e0ed45ce504`, 2026-11-06 PST. #227 was merged by the user as `31348fcf7dee32f84db1fc8f929d80653137995e`. The external S2 worker is Claude; its brief is being prepared, not yet dispatched. The host proof is `sorry`, assigned to the **external S2 fill** under Q4 (B); it is not proved or dispatched by this registration. The user dispatches S2 after gate closure and #227's merge. Registered 2026-11-06 PST. | **dl-a:** `polyTimeComputable_expSampleRaw`; **dl-c:** `dlc_numPoly_sample`, serving ElGamal generators/encryption; **rsa:** the unit sampler and `rsaGenRaw`; **rabin:** the prime/Blum-prime generators, with the tail bound feeding padding. S2 replaces their four private rejection loops and refreshes the six sketches (Q7). |
| H16 | **Counted word loop at the FP layer:** `Complexity.BinArith.forLoop`, `forLoop_pairEncode`, `polyTimeComputable_forLoop`, and `forLoop_bound_of_ctx` in `TCSlib/Complexity/ClassP/BinaryArith/Loops.lean`. On a paired state it runs a polynomial-time leaf once per counter letter. The caller supplies a polynomial bound on all intermediate argument words. The retained-context corollary derives this bound from context preservation and linear growth. For the same result function on every raw word, apply H14's `Turing.ModuleHost.clean_install` to `polyTimeComputable_forLoop`. Its clean call installs the result by its polynomial first-halt budget, and `Clean.envelope` bounds every work head at every time by that same budget. | Existing public proofs. This registers their composition for the counted-loop contract and its clean-call time and head envelope. Gate 14 reviews this registry entry before the consumer fills. | Polynomial-time Boolean expansion, packed and scheduled dot products, matrix row steps and matrix-vector evaluation, SIS collision-output postprocessing, and the composed SIS hash evaluator. |

**The received ARM machinery, H7–H13** (registered 2026-10-14: the ARM fill gate's round 2,
finding 5; user decision 3). The rows' public contracts, with file and line, are in
`campaign/fills/arm/evidence/arm-fill/r2/registry-rows.md`. Its lines are at `e831b5b0`, with one correction:
`vword_whole₁` is at `Logspace/InputAccess.lean:93`, not 90.
- **Accepted exception.** Their first uses, the consumers named above, all inside the delivery
  `8c23f3bc`, are an accepted exception to *hosts come first*: they were not statement-gated
  before their consumers were written.
- **Gate before reuse.** No further consumer of H7–H13 is briefed until that row's public contract
  has passed a contract gate, of the contract as listed or of its generic form.
- **Named consumers** are direct importers and named transitive users, marked as such.
- **Generic forms** are ARM-2's direction (backlog §1 ARM-2), designed with Hydroxyi.

**C1's hosts (landed 2026-10-14, PR #87; gate `campaign/gates/12-c1-hosts-statements/findings.md`).** The
nondeterministic phase host `NDTM.phaseHostND` (`Build/NDHost`), the choice writer `ndWriterTM`
(an H5 device), the window copier `exists_inputWindowCopyTM` (`Build/InputWindow`), the
interpreter core `R` = `exists_ndInterpreterCore` (`NDCodeSimulator`) and the exhaustive decider
`E` = `FinNDTM.exists_exhaustiveDecider` (`ClassNP/ExhaustiveReplay`); their contracts are
sorried for the C1 fills.

Pure-Lean kits that the hosts' semantics share (not machines, so not hosts,
but designed with them): bounded reachability (`ReachWithin`, the midpoint
lemma, pigeonhole shortening) with bridges from configuration reachability,
`GraphReach` and `Kruskal.Reach` to Mathlib's `Digraph`/`SimpleGraph`.
Consumers: Savitch, TQBF hardness, Immerman–Szelepcsényi, PATH, §15. The received code added
four more reachability notions, each with its own consumer: `WalkLe`, `SavitchARM.Reach`,
`ExpBFS.RCode` and `TQBFHard.Mid`/`mid_iff_steps`. The bounded-reachability kit, when designed,
bridges them (2026-10-14).

**Work in flight when the rule was adopted.** No in-flight brief is withdrawn.
B4 membership and B5a H1 received addenda (`campaign/fills/ch34/briefs/ch34-b4-mem-addendum-1.md`,
`campaign/fills/b5a/briefs/b5a-fill-h1-addendum-1.md`): their hosts stay private for now, as
their ownership requires, but are written generic, with self-contained
statements, and listed as promotion candidates. They and S1b's candidates are
promoted, by PR and gate, before any second consumer is briefed.

**Proposed sequencing** (maintainer; for the user): item 0, then H1 (two
consumers ready: TQBF membership and Savitch), then H3/H4 from S1b's delivery,
then H5 with H2's self-application universal for B6, then H6 for TQBF
hardness. Each is a statement phase plus its gate, then a fill.

## 15. The programming layer (commissioned by the user, 2026-10-12)

**Decision.** "Support a programming layer now, now that we've got the really
low level stuff working" (user, 2026-10-12). This supersedes §1's non-goal.

**Why now.** The routine layer (§12), framed contracts (§12.6), counter loops
(§12.7), configuration records and tables (§12.8, §12.8b) and the zone and
virtual-input layer (§13) are proved or being filled. What is missing is any
way to write an algorithm once and get a machine with a proved bound:
- `CounterProg` has unary registers, `inc`/`dec`/`jz`/`out`/`pr` and a one-way
  input, compiled with a `t(2t + 3)` overhead (`CounterProgRun.lean`). It
  serves emitters, but cannot hold a string, an array or a graph;
- `LogProg.ARM` has `O(log n)`-bit registers and yes/no answers, and compiles
  for space only;
- the `PolyTimeComputable` closure algebra is `Bool`-only and existential;
- none of the three is built on `Build/`, and none is registered in
  `ComputationalModels.lean`.

So every machine-level algorithm is a hand-built host (§14), and an
introductory algorithms curriculum (graph search, shortest paths, MST,
sorting, with running times) cannot be written at all. The only
cost-annotated code, the `TimeM` in `Cryptography/RSA.lean`, charges trusted,
unchecked costs.

**Goals.** Write an algorithm once, as a program, and obtain: its semantics;
a step count that is sound by construction (only primitives charge cost);
and a compiled `FinTM` with a proved time bound polynomial in the program's
cost and a space bound linear in its register footprint, feeding `∈ P`,
`PolyTimeComputable` and `SPACE` memberships. The compile theorem is proved
once, from the contracts of the rows and hosts, never by tracing runs.

**Proposed architecture** (maintainer draft; decisions 15.x below):

```
L4  Algorithms     TCSlib/Algorithms/: curriculum algorithms, specs against Mathlib
L3  Programs       a deep-embedded structured language over word registers (+ arrays),
                   big-step semantics with cost, compile theorem to FinTM
L2  Contracts      the framed-contract structure (§14 item 0) and the registered hosts
L1  Routines       Build/: catalog rows, scans, seams, loops, records, tables
L0  Model          MultiTapeTM / FinTM, the run calculus
```

- **L3, programs.** Registers hold words over a finite alphabet, one tape
  each. Instructions are the catalog's word operations (copy, clear, append,
  compare, binary increment, add and `≤`, seek within delimited fields), reads
  of the native input, clean calls of `ComputesFunInTime` machines on
  registers, structured control (sequence, `if` on a register test, a bounded
  `for` over a register's value by counter loops, `while` with fuel), and
  calls of registered hosts. Each instruction is charged by its row's cost in
  the register lengths. Arrays and maps, in a later increment, are record
  tables (§12.8b) with charged access.
- **L4, algorithms.** Written in L3 when machine-faithful costs are the point,
  or as functional code over a cost model that is sound by construction (a
  query or operation monad whose primitives are the only cost source), with
  specifications against Mathlib (`List.Sorted`, `List.Perm`,
  `SimpleGraph.Reachable`, `Digraph`). The comparison-query form also states
  the sorting lower bound. `RSA.lean`'s `TimeM` (colleague-owned) is a
  candidate to relocate or replace here, after a provenance check
  (`backlog.md` §5).
- **Existing layers.** `CounterProg` and `LogProg.ARM` stay; each is bridged to
  L3 or re-based on it (15.4). The new models are registered in
  `ComputationalModels.lean` (policy §1, model registry).

**Open decisions (15.x, for the user).**
1. **Embedding.** (a) A deep embedding: syntax, semantics and a verified
   compiler (cost-sound by construction, the most reusable, the largest); or
   (b) shallow: programs are compositions of §14's contract structures
   (cheaper, but no syntax to reason about or teach from). Maintainer lean:
   (a), compiling into (b).
2. **Register alphabet.** `Bool` only, or any finite alphabet with
   `alphabet_reduction` at the end.
3. **First memory model.** Registers only, or registers plus record-table
   arrays from the start.
4. **`CounterProg` and `LogProg.ARM`.** Bridge, re-base, or leave as they are.
5. **Curriculum cost model.** A comparison-query monad first (sorting), an
   operation monad (graphs), or curriculum algorithms written in L3 directly.
6. **Shape of the compile bound.** Per-instruction affine in the register
   lengths (`C·(cost + n + 1)` overall, with register lengths bounded by the
   cost), or a polynomial.
7. **First consumers** (rule of admission, §4: two named customers). Proposed:
   machine side, the `NL ⊆ P` BFS (or `PATH ∈ P`) and TQBF membership or
   Savitch; curriculum side, merge sort and BFS.

**Prior art examined (2026-10-12; nothing taken yet).** Two formalizations of the
same result, Alman and Vassilevska Williams, *Truly Subquadratic 3SUM and Truly
Subcubic APSP via Triangles in Sparse Lopsided Graphs* (arXiv:2610.06783v1). Both
are word-RAM developments with a structured language, a program logic and a
verified compiler:
- **[AFM26]**: `anthropics/formal-math`, folder `3sum-apsp`, commit
  `e1a4e6508154ea59f030480661590a9fe3018011` (2026-10-05), Apache-2.0, © Anthropic,
  PBC, on Lean and Mathlib v4.33.1. It has 434 Lean files and 102,310 lines. Its parts:
  - the trusted `EndStatement.lean` (139 lines, core Lean only);
  - the language, logic and compiler in `Lang/` (about 9,000 lines) and `Machine/`
    (about 840);
  - the paper's algorithms as verified programs in `Programs/` (about 52,600).
- **[Xuanji26]**: user **xuanji on prove2me** (citation as directed by the user),
  file `3sumapsp_example.lean`, examined locally. It is the top-level assembly of a
  stronger 3SUM bound, `O(n^1.999074)` against [AFM26]'s `O(n^1.9992)`, which comes
  from an Exact Triangle saving of `9261/5000000`. The file builds on [AFM26]'s
  library: 264 of its 265 module docstrings and 125 of its 128 theorem blocks are
  verbatim in [AFM26]. Its 62 project imports, including the module that proves the
  improved saving, are not in the file.

The designs that §14 and §15 may adapt from them are:
- the program logic (`Ends`, `Meets`: postcondition predicates, time "within `T`",
  handed on rather than added up, and spec-only calls);
- the `SameOn` framing with `.keep` lemmas and default-argument tactics;
- tasks, solvers and hosts (`IsHost`);
- run limits built into the semantics;
- the `DetTimeModel` claim algebra;
- the asymptotics calculus with its `growth` tactic.

If adapted, they are cited per `policy.md` §2, *Design adaptation*: [AFM26] as the
origin of the design, and [Xuanji26] for the file the user supplied.

**Sequencing.** 15a: the contract structure (shared with §14). 15b: L3 with
registers only, its semantics, cost and compile theorem (a statement phase and
its gate, then fills). 15c: arrays over record tables. 15d: the curriculum
layer's first increment (cost model, merge sort with `≤ n⌈log₂ n⌉`
comparisons, BFS with an `O(n + m)` operation count). Every Lean step is a PR
plus its own gate.

### 15a. Language first; the spike (user decision and maintainer draft, 2026-10-12)

**Decision (user, 2026-10-12): language first.** The remaining results that are
algorithms are written as programs of the §15 language and compiled. (§16, decision 3,
confirms this for Savitch and `NSPACE ⊆ DTIME(2^O(S))`, which need machine-configuration routines
in the language.) These are
Savitch's recursion, the AND/OR evaluator (H1), graph search (H4), and the
intro-algorithms curriculum. The hosts that are *about machines* stay at machine
level and proceed now: H2 (step block), H3 (windowed runner), H5 (input devices)
and H6 (machine-to-formula). Work in flight is unaffected. S1b's BFS and B4's
walker finish as briefed, and may later be re-derived as programs.

**Architecture (proposed): two stages, as in [AFM26].**

```
program of the language  --stage 1-->  flat word-RAM program  --stage 2-->  FinTM Bool
                        (compiler; constant          (one simulation; polynomial
                         overhead, no tapes)          overhead, the only tapes)
```

- **Stage 1** is pure program reasoning and never mentions tapes. [AFM26]'s
  compiler from its language to its word RAM is about 2,500 lines. Its theorem
  says a run of `c` steps becomes at most `startCost + stepsPerStep·c` RAM steps,
  with constants that depend only on the program text.
- **Stage 2** is the only place tapes appear: one machine simulates a fixed RAM
  program, one instruction at a time. The RAM has about a dozen instruction
  kinds, so the tape-level proof surface is about a dozen instruction contracts
  (§14 item 0), one dispatcher over the program counter (the phase host), and one
  simulation induction.
- **The word RAM is a model in its own right**, registered in
  `ComputationalModels.lean`. In it the curriculum's statements have faithful,
  constant-factor costs. Stage 2 then turns them into P, PSPACE and L
  memberships.

**The language.** It is [AFM26]'s light language:
- integers and numbered local variables, with a flat memory `ℕ → ℤ`;
- expressions: constants, `+`, `−`, `×` and loads; tests `<` and `=`;
- statements: skip, assignment, store, sequence, if, while, and procedure calls,
  with recursion;
- unit costs per constant, variable, operation and load;
- the limits `word`, `space` and `depth` as part of the semantics;
- the logic `Ends`/`Meets` with its rules, frames and tactics.

It adds three things that our classes need:
- `inBit e` and `inLen`, which read the input string *in place*, never copied
  (logspace needs this);
- `emit e`, which appends a bit to the output, for reductions and function
  problems;
- possibly `half e`, cheap on both targets (decision 15a.4).

**The RAM.** It is [AFM26]'s `EndStatement.Instr`:
- `one`, and `add`/`sub`/`mul` modulo `2^W`;
- `load` and `store` (indirect);
- `bltz`, `accept` and `reject`.

It adds `rdIn` (an input bit at a computed position), `len` and `emit`.

**Stage 2's theorem (statement shape, draft).** For a RAM program `P` there are a
`FinTM Bool` machine `M` and a constant `A` (depending on `P` only) with the
following property. Whenever `P` halts on input `x` with word size `W` within `t`
steps, touching `f` distinct cells:
- `M` halts on `x` with the same verdict and output within
  `A·(t + 1)·(f·(W + a) + W² + |x|·log|x| + 1)` steps, where `a` is the width of
  an address;
- `M`'s space is at most `A·(f·(W + a) + W + log|x| + 1)`.

The per-step cost is dominated by one scan of the memory table, a
shift-and-add multiplication, and one input seek.

**What consumers get.**
- **P:** polynomial cost and limits give membership in P.
- **L:** `O(1)` cells, bounded depth and `W = O(log n)` give space `O(log n)`,
  because the input is read in place.
- **Savitch:** depth `O(S)` with `O(1)` locals of `O(S)` bits gives `O(S²)`.
- **TQBF ∈ PSPACE:** depth `O(n)` with `W = O(log n)` gives `O(n log n)`.

Results that need tight *linear* space may still want direct machines.

**Reuse from `Build/`:**
- the phase host, for dispatch on the program counter;
- the framed copy, compare, clear and increment rows;
- the `scanTM` carry family, for binary addition;
- `exists_inputSeekTM` and `exists_inputLengthTM`;
- counter loops, for the rounds of a multiplication;
- R1 embedding and `alphabet_reduction`.

**New rows needed:**
- two-tape addition and subtraction modulo `2^W`;
- multiplication;
- a sign test;
- find-by-key in a memory table, where the key is a word on another tape. The
  record-table find takes a finite-state predicate, so it does not cover this;
- in-place overwrite of a fixed-width field.

**Rough cost** (maintainer estimate, in lines):
- item 0's contract structure: 1,500–2,000;
- stage 2: 6,000–10,000;
- stage 1 with the language, logic and tactics: 5,000–7,000 if ported from
  [AFM26], more if re-implemented.

That is about 15,000–20,000 lines in all, or a few fill waves: about the size of
S1b plus the record tables.

**Open decisions (15a.x, for the user):**
1. **Two stages** (recommended) or a direct compiler from the language to machines.
2. **Port or re-implement [AFM26]'s language, logic and compiler.**
   - *Port:* Apache-2.0, vendored with its header, the upstream commit and a list
     of local modifications (`policy.md` §2, *Vendored code*).
   - *Re-implement:* follow the design, with a *Design adaptation* citation.

   A port is not mechanical. [AFM26] uses Lean v4.33's module system (`module`,
   `public import`, `@[expose] public section`), which our pin v4.25.0 and its
   Mathlib do not use. Porting means removing that layer and repairing
   Mathlib API drift. A port trial on the core (syntax, logic, rules, frames,
   calls, tactics and regions, about 1,900 lines) would settle it.
3. **The RAM's input convention:** read in place by instruction (recommended;
   logspace needs it), or loaded into memory as in [AFM26] (kept as a variant
   for curriculum statements).
4. **Halving** (`half e`) in the language and the RAM: yes or no.

**Next step after 15a.1–15a.3.** Statement drafts of item 0's contract structure
and of stage 2's theorem, as sorried Lean in a scratch worktree, with a pre-ship
elaboration check. Then a statement gate.

### 15b. The port of [AFM26]'s language, logic, routines and compiler (user decision, 2026-10-12)

**Decision (user, 2026-10-12): port it.** The user asked two things first:
- *Does their core serve our purposes?* It serves all of the language-first list, which is
  deterministic. Nondeterminism and randomization are not covered and become one planned
  extension, the coin stream (below).
- *Does their licence allow it?* Yes: Apache-2.0, as tcslib is. Vendored files keep their headers,
  list their changes, and carry the upstream `NOTICE` (repository `NOTICE`).

**The trial port**, read-only, with no build products:
- **Core and routines.** The language core with the merge-sort and power-table closures (18
  modules, 3,681 lines) elaborated at our v4.25.0 pin with 0 errors.
- **Compiler.** The compiler's correctness closure (23 modules, 5,565 lines) also elaborated with
  0 errors.
- **Axioms.** `sort_meets`, `merge_meets`, `powTable_meets`, `time_split`,
  `compileProgram_correct` and `sim` depend only on `[propext, Classical.choice, Quot.sound]`.

**What is vendored.** `TCSlib/Programs/` holds 41 modules (8,548 lines of the trial set) plus
`Compat.lean` and the facades `Programs`, `Programs/Util`, `Programs/WordRAM` and
`Programs/Light`:
- the language, its logic and tactics (`Light/`);
- 14 verified routines (`Light/Lib/`): copy, fill, merge, merge sort, counting sort, radix
  pass, logarithms, powers, modular reduction, square root, odometer and others;
- the compiler to the word RAM (`Light/Compiler/`, with `compileProgram_correct`);
- the word RAM and its run facts (`WordRAM/`);
- general list and index facts (`Util/`).

Their sieve is deferred: it needs `Nat.primesLE`, which our Mathlib pin lacks. The port is the
41-module import closure of the roots named in `scripts/vendor_afm26/README.md`. Two generic
upstream modules outside that closure are **deferred**, not excluded on principle (fidelity
gate, finding 3):
- `Lang/Renumber.lean` (procedure relocation), a candidate for the compiler extensions;
- `Machine/Footprint.lean` (read/write footprints), a candidate input to stage 2's space bound. The files are
generated by `scripts/vendor_afm26/` from upstream plus a recorded list of changes. The
per-file diff is `campaign/gates/programs-vendor/evidence/upstream-to-vendored.diff`, and the file map is
`.../file-map.md`.

**Local modifications** (listed in each file's header):
- the Lean module-system syntax removed, as in the cslib precedent;
- namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp`
  to `Light`;
- `EndStatement.lean` trimmed to the word RAM;
- `## References` sections and the standard options added;
- `with_unfolding_none`, absent in v4.25, replaced by `with_reducible`. This is an approximation:
  it keeps reducible definitions unfoldable, and every vendored proof passes with it;
- nine v4.25 proof repairs (`scripts/vendor_afm26/fixes.py`). Seven insert a beta reduction,
  because v4.25 leaves an instantiated motive or invariant unreduced. One rewrites a cast step,
  and one completes a `split_ifs`;
- three renamed lemmas provided in `Compat.lean`, each to be removed at the Mathlib bump that
  provides it.

**Checks.**
- The shipped files, concatenated, elaborate with 0 errors together with all fifteen
  `Complexity` facades and `ComputationalModels`. They declare 2,990 constants, none of which uses
  `sorryAx`, and no axiom.
- A textual screen of the 713 new public names against the other areas finds no clash.
- The style lint reports 0 FAIL and 0 WARN over the 45 files. The vendored files are registered
  as such.
- The user-run replay compiles each module separately, in dependency order
  (`campaign/gates/programs-vendor/evidence/replay-order.txt`). Its first run found one import gap.
  `Util/Index` uses a Batteries lemma that upstream reaches through its imports at Mathlib v4.33
  and ours does not; 16 modules failed with it. The fix is an added
  `import Batteries.Data.Nat.Lemmas`, listed in the file's header.
- The concatenated check had masked that gap: its union of all files' imports contained the
  lemma. A per-module closure check now elaborates each of the 46 modules and facades in exactly
  its own import environment (`scripts/vendor_afm26/closurecheck.py`), and all 46 are clean
  (`campaign/gates/programs-vendor/logs/programs-vendor-closure-check.log`).
- **Replay passed** (user-run, at `155255ed`; `campaign/gates/programs-vendor/logs/programs-vendor-replay.log`). All 47
  entries are clean, with 0 errors and no `sorry` warnings: the 42 modules, the four facades and
  `ComputationalModels`. The resumed run rebuilt the 17 modules that had failed and skipped the 30
  that were already clean.

**Models registered** in `ComputationalModels.lean`: `Light.Program` and `WordRAM.Instr`.

**Next, each a statement phase with its gate:**
1. the extensions: reading the input in place (`inBit`, `inLen`), `emit`, and the coin stream
   (`coin x`, read for each fixed stream, so that the deterministic logic and compiler carry
   over; nondeterminism and randomization then quantify over the stream);
2. stage 2, the RAM-to-`FinTM` simulation, with the contract structure (§14 item 0);
3. the first consumers.

### 15c. The language and RAM extensions: semantics decided (user, 2026-10-12)

A read-only survey of the vendored layer (2026-10-12) costed the four extensions and their
options. **Decision (user): all four go into one scripted vendored edit set**, with the
survey's recommended semantics:

- **Input read in place.** A statement `x := inBit e` (cost `e.cost + 1`; past the end it reads
  `0`) and a RAM instruction `rdIn`. `inLen` comes first from an argument cell (`|x|` passed as
  argument `i`, which needs no change); a `len` instruction follows only if a consumer needs it.
  Statements rather than expressions, because expression code must be `Straight` and `effect`
  touches only memory. The input string goes into `Limits` (never constructed in the port,
  so nothing breaks), and `Fits` gains `|x| ≤ word`. Stage 2 maps `rdIn` to
  `exists_inputSeekTM`, and `load` stays a table lookup. The rejected options were mapping the
  input into memory at the RAM level, and keeping [AFM26]'s memory-loaded input, which forces
  `lim.space ≥ n` and so rules out logspace.
- **Where the I/O state lives: new indices of `Exec`.** The bits emitted (`o`) and the coins
  consumed (`r`) become indices of the big-step relation, concatenated by `seq` and `while` and
  passed through `call`. `Ends` keeps its type, hiding them under `∃`, so `Meets` and the 14
  routines are untouched; a new `EndsIO` lets a postcondition see them. Six files mention
  `Exec`, against about 124 state literals in 24 files had the state grown instead.
- **Coins read once**, as a consumed `List Bool`. `coin x` sets `x` to either bit at cost `1`,
  consuming it. For a fixed stream `ρ`, `EndsIO ρ` asks for a run whose consumed word is a prefix
  of `ρ`. Nondeterministic acceptance is "some `ρ` of length `T` accepts". Randomized
  acceptance uses `randProb` over `Fin m → Bool`, which needs a determinism lemma for `Exec`
  (not yet stated). **Time bounds are uniform over all streams**, as `NTIME` and `NSPACE`
  require. Read-once coins are also right for NL and BPL, where two-way access to the coins
  would give NP's power, and they compile to both kinds of target. Stage 2 makes each `coin` one
  NDTM choice step; for BPP it produces a deterministic machine that takes the coins as a second
  input.
- **`emit e`** appends a bit to an append-only output, mirroring the machines' per-step output.
  Strictly, only space-bounded output (log-space reductions) needs it; time-bounded functions
  can use memory output. It is included now because it changes the same signatures.
- **`half e`**, as a statement and a RAM arithmetic-shift instruction (not an `Op`: `Op` is
  binary, and its effect lemma needs a range hypothesis). It is `O(W)` in stage 2 and helps
  configurations packed into words.

**Estimated size:** 600–1,000 lines of vendored edits, made by the generator scripts in
`scripts/vendor_afm26/` and listed in each file's header, plus 700–1,150 new lines (the `EndsIO`
rules and tactics, acceptance and probability, the determinism lemma, the new `sim_*` cases).
Every new construct needs a case in each exhaustive definition and induction over `Stmt`,
`Exec` and `Instr`. The hardest parts are carrying the output and the coins through the compiler
simulation, and threading the input through the RAM's run calculus.

**Obstacles the survey found** (backlog PROG-2, PROG-3):
1. **No footprint along a run.** `compileProgram_correct` and `Finished` describe only the final
   memory. Stage 2's space bound needs every intermediate memory inside `[-lowCell, lim.space)`.
   That needs a stronger `Steps`, or the deferred `Footprint.lean` (PROG-1(e)). L and Savitch
   need it, whatever the extensions.
2. **`Ends` is existential.** With a nondeterministic coin rule, specifications that mention I/O
   need `EndsIO` with an explicit stream, and probabilities need the determinism lemma.
3. **`Fits` has no input-length clause** (above).

**Corrections to §15a and §15b, from the survey:**
- the RAM has nine instruction kinds, not "about a dozen";
- the RAM additions are `rdIn` (with `len` later), `emit`, `coin` and `half`;
- the deterministic logic and compiler do not carry over unchanged for coins: the stream
  position is state, carried here by `Exec`'s index;
- [AFM26]'s memory-loaded input is not in force in the port: `SolvedBy` was dropped, `loadWords`
  is unused, and the compile theorem takes any memory satisfying `Input`;
- logspace from `O(1)` cells holds only with input read in place, and only once obstacle 1 is
  closed.

### 15d. Stage 2, PROG-2 and PROG-3: statement drafts (2026-10-12)

A maintainer sub-agent drafted the statements, and the maintainer re-elaborated them: 0 errors;
the only warnings are `sorry`s. They are evidence, not landed files:
`campaign/items/stage2/Stage2Draft.lean.txt` (723 lines),
`campaign/items/stage2/ExtensionsDraft.lean.txt` (415 lines), and the notes
`campaign/items/stage2/NOTES.md`.

**Stage 2 (PROG-4).** It is drafted in two forms:
- `exists_simulation`, deterministic;
- `exists_ndSimulation`: each `coin` is one `FinNDTM` choice step, with bounds uniform over all
  coin streams.

Both are stated over a draft RAM that wraps the vendored one: the nine vendored instructions, plus
`rdIn`, `emit`, `coin` and `half`. With `n = |x|` and `W = W n`, the bounds are
`T = TW n + A·(t + 1)·(f·(W + 1) + W² + n + 1)` and
`S = SW n + A·(f·(W + 1) + W + logSpace n + 1)`.
- **The word size** is a hypothesis `WordSizeComputable W TW SW`: some machine outputs
  `Nat.bits (W n)` within `TW n` steps and `SW n` cells. Two bridges supply it: `c·logSpace`,
  from the input-length counter R8.5c, and `c·S`, from `SpaceConstructible`.
- **The corollaries:** DTIME and P, SPACE and LOGSPACE, log-space transducers, Savitch's
  `SPACE(S·S)`, NSPACE and NL.

**PROG-3.** `compileProgram_footprint`: a compiled run stays inside `[-lowCell, lim.space)`, its
reads included. The gap is only at the RAM level, where `Steps` and `Finished` speak of the final
memory.

**PROG-2.** A self-contained mirror of the four new statements and of `Exec`, with the output word
and the consumed coins as indices; `EndsIO` with 15 rules; the determinism lemma; acceptance and
`acceptProb`. `NOTES.md` §5 lists, by file and line, every exhaustive definition and induction
the real edit must extend.

**Corrections to §15a and §15c, read off the code:**
- there is no separate address width, because addresses are words (`WordRAM/Basic.lean`);
- the input seek row is linear (`exists_inputSeekTM`), so the per-step seek term is `n`, not
  `n·log n`;
- the word size's own computation is charged once, as `TW` and `SW`;
- `inBit` needs no input-length clause in `Fits`;
- `Exec.bounded` needs `1 ≤ lim.word`;
- 38 lines of `Logic`, `Rules` and `Assigns` (28, 8 and 2, read line by line in the stage-2
  statement pack; the drafts estimated about 32) build or take apart `Ends` witnesses, so "the
  routines are untouched" holds for `Meets` and the library, not for those files.

The nondeterministic form's fill also needs one lemma not present today: a nondeterministic run
agrees with the deterministic one on states whose two transitions coincide. This is the
nondeterministic contract variant that §16 lists as later.

**Estimate** (not measured): about 9,500–15,000 lines beyond MIG-0a, made up of PROG-2
1.4k–2.3k, PROG-3 0.75k–1.35k and stage 2 6.1k–10.5k.

**Open questions for the user**, each with the drafter's recommendation (`NOTES.md` §6):
1. extend the RAM by a wrapper (recommended) or in place, which breaks about 50 configuration
   literals;
2. add `Exec`'s indices in place (option A, recommended, as §15c decided) or as a new relation
   (B);
3. `WordSizeComputable` with its two bridges (recommended), or `SpaceConstructible` directly;
4. `emit` appends "nonzero", and the footprint counts touched cells (both recommended as
   drafted).

**Answered (user, 2026-10-12): all four as recommended.** The RAM is extended by a wrapper, the
`Exec` indices are added in place (option A), the word size is `WordSizeComputable` with its two
bridges, `emit` appends "nonzero", and the footprint counts touched cells.

**Statement gate (2026-10-13):** `campaign/gates/10-stage2-statements/pack.md`. The maintainer re-elaborated
the landing form (0 errors; the only warnings are `sorry`s). It differs from the drafts in:
- **homes:** the wrapper in a new `Programs/WordRAM/Extended.lean`, below the compiler, because
  after PROG-2 the compiler emits `XInstr`; PROG-3's compiler-level statements as local
  modifications of the vendored `Simulation.lean` and `WholeProgram.lean`, because their proofs
  need private lemmas; stage 2 and its corollaries in a new topic `Complexity/RAMSimulation/`;
- **`startMem` is renamed `initMem`**, because the vendored compiler declares
  `Light.Compiler.startMem` and opens `WordRAM`;
- **footprints of at most `3n` cells**, so that `mem_P_of_decides` drops its cell bound;
- **the slice lemma and its space companion are stated** (`NDSlice`). The slice lemma is
  already proved, with a pointwise form of the same hypothesis, in C1's host draft
  (`campaign/items/c1/C1HostsDraft.lean.txt`, `Turing.NDTM.runWith_eq_fixChoice_runFrom`); the
  stage-2 pack does not say so. One copy lands, in `Nondeterministic.lean`, with C1's proof under
  the gated statement (maintainer note, 2026-10-13). **Both are proved** since C1's landing
  (PR #87, 2026-10-14);
- **PROG-2's edit list is longer:** under the wrapper, the compiler's code type becomes
  `List XInstr` at the sites the pack lists.

**Gate CLOSED** (round 1, 2026-10-14: 0 blockers / 0 majors / 4 minors;
`campaign/gates/10-stage2-statements/findings.md`, resolutions `campaign/gates/10-stage2-statements/resolutions.md`).
The homes, the namespace `WordRAM` and `initMem` are approved. PROG-3's compiler-level statements
(B1, B2) may land now, with their extended forms re-gated at PROG-2, or with PROG-2. The
auditor prefers `acceptProb` in a Complexity-side module. Next: the landing PR.

## 16. The foundation migration (user decisions, 2026-10-12)

**Why.** The user: "I really think we should invest effort into building code in the right way,
especially in this foundational stage." Seven read-only reviews of the tip `9827cc99` costed a
retroactive migration onto the §14/§15 style:
- the Build foundation and the machine core;
- the machine-level files that stay on Turing machines;
- the algorithm files that could become programs.

Their per-file figures are the restyling backlog (`backlog.md` §2, MIG/RS).

**Decisions (user, 2026-10-12).**
1. **The no-retroactive-migration rules are lifted for this migration**: §8's byte-identity
   bullet and decision 12.2's byte-identical `Primitives.lean`.
2. **Scenario B.** Proof bodies are swapped onto contracts, and in addition the duplicate
   statement families are retired: the R3 canonical `_run` rows, `counterLoopTM` next to
   `counterLoopTMVia`, `EmitIterEmbed`'s embedding, and `Codes2Tape`'s mirror. Their consumers are
   edited. Proof-body swaps under unchanged statements are gated by a freeze check, a replay and
   a fidelity gate. Each retired or changed statement needs a full statement gate.
3. **Savitch and `NSPACE ⊆ DTIME(2^O(S))` are algorithms at heart.** They are written as programs
   of the §15 language and converted by the RAM-to-`FinTM` compiler (stage 2). TM-intrinsic
   results are *not* recast as programs: Cook–Levin, TMSAT, NP ⊆ PSPACE's machine,
   Nondeterminism, the oblivious and hierarchy constructions, and the universal machine.
   **S1b**, in flight at machine level and proving `NSPACE ⊆ DTIME(2^O(S))`, `NL ⊆ P` and Ex 4.3,
   **finishes as briefed** (user, 2026-10-12: "Let it finish"). Once stage 2 and the
   configuration routines exist, it is re-derived as a program and its private host retired,
   with its public statements unchanged (MIG-19).
   *Outcome (fills-6, user: "Stop at this partial"):* S1b landed `NL ⊆ P` and Ex 4.3 proved
   modulo `NSPACE ⊆ DTIME(2^O(S))`, without a search host. MIG-19 is now the route for the
   simulation itself.
4. **Restyling is opportunistic, with a clear backlog** to chip away at: the RS items. Each
   row has its estimate, prerequisites and gate.

**The estimate** (ranges are the reviewers'; ESTIMATED unless marked):

| Bucket | Today | Net change |
|---|---|---|
| Foundation: Build (43,143) and the core (3,887), MEASURED | 47,030 | about −12.5k (−8k to −17.5k). That includes the `f2_` deletion, −7.6k to −8.3k at high confidence, and about 3.6k of new infrastructure |
| Machine-level files staying on TMs: universal, robustness, Nondeterminism, diagonalization and time hierarchy, oracle model, Mathlib bridge | 26.3k | about −4k to −5k: −3.7k from restyling, −1.7k to −2.1k from duplicates found, and +0.5k to 1.5k of extra infrastructure |
| Scenario B's statement retirements | | about −1k more |
| **Total** | **73k** | **about −17k (−12k to −23k)**. About 30k lines of proofs are touched and 4–5k are written new |

**What the contract structure must support** (§14 item 0). The survey revises the "time within
`T`" default taken from [AFM26]'s program logic:
- **exact time, with a no-earlier-exit cut, as first-class fields**, and "within `T`" derived
  from them. About 34 public Build statements carry cuts and about 33 state exact times. Seams,
  counter loops and the zone layer's `2p + 2` compose exact times;
- a **positive-duration field**, for the universal machine's block converse;
- an **endpoint function and a frame predicate**, with tape-indexed `SameOn`-style frames and
  `.keep` lemmas;
- **head envelopes**, both radius and interval forms, with space derived from them;
- the **input tape** (clamped moves, virtual input) and **output appends**;
- **transports**: state renaming (`Sum`/`Sigma`), R1 embedding, symbol lift, alphabet reduction,
  and the lockstep combinators of the robustness layer (decoration, parallel coding, folding);
- **later**, nondeterministic (`runWith`) and oracle-step variants.

From [AFM26] the design takes framing, spec-only calls and default-argument tactics; it does not
take the treatment of time.

**Programs for Savitch and `NSPACE ⊆ DTIME`** (decision 3) need one more planned component:
**machine-configuration routines in the language**. A configuration of a given (nondeterministic)
machine is encoded in memory, and routines enumerate its successors, or test the step relation,
from the machine's finite table. This is narrower than a general machine interpreter, since the
programs are built per machine.

Savitch's `O(S²)` space is **decided (user, 2026-10-12; §16b item 1)**: configurations are held
as single words, with word size `Θ(S)`, so that `O(S)` frames times `O(S)`-bit words fits the
planned bound of cells times word size. Stage 2 therefore takes a computed word size. A
bit-accounted space bound in the compile theorem was declined.

`NSPACE ⊆ DTIME(2^O(S))` is unaffected, since polynomial overhead on `2^O(S)` stays `2^O(S)`.

**Order of work:**
1. Item 0's statement phase and gate, with the requirements above.
2. The certain savings, which need no new infrastructure: named witnesses and the `f2_` deletion
   (MIG-1), then the known duplicates (MIG-2 to MIG-10).
3. Contract instances and tactics, grown against the first migrated file; then rebasing the
   composition-heavy files (MIG-11 to MIG-17).
4. The asymptotics port (MIG-18).
5. The RS items, opportunistically.

**12.2c** (plan §4e) is folded into this migration. Its items are subsumed, moved, kept as MIG-20
and MIG-21, or lapsed, as recorded at the head of the 12.2c tasklist. **MIG-0 and MIG-1 now
precede §13d G2** (user, 2026-10-12), reversing "G2 comes before the Catalog split".

New and unfinished work is written in the new style from the start. Deliveries now in flight
in the old style (record tables, W2-S, B5a canonizer and H1, B4, S1b) join step 3.

### 16a. MIG-0, the contract structure: statement draft and decisions (2026-10-12)

**A sorried statement draft of `Build/Contract.lean` was written and fit-tested** (maintainer,
2026-10-12). It was informed by a read-only inventory of every public contract in `Build/`
(about 150 run statements: 24 exact closed-form times; about 45 cuts that include time `0` and
4 that do not; 25 interval and 12 radius envelopes; no frame predicate anywhere, and frames
written in four idioms).

**The structure** `Turing.Contract M entry exits ι x`:
- a precondition, an **exact time**, an **endpoint function** and per-tape head intervals
  `[lo, hi]`, all functions of a data index `i : ι` (the word or fields the module reads) and the
  start configuration;
- proofs: the run reaches the endpoint at that time; the endpoint is at an exit; **no exit is
  reached earlier, with the cut including time `0`**; and the heads stay in their intervals.
  Exits form a set, so single anchors, verdict pairs, loop exits and halting are one structure;
- derived: "within `B`" (`within`) and the per-tape space bound (`spaceUsedByTape_le`, through
  `spaceUsedByTape_le_card_Icc`); positivity is a predicate.

**Decisions (user, 2026-10-12):**
1. **Universe `Type`** for the alphabet, the states and the data index: the universe of
   `FinTM`, `phaseHostTM` and `counterLoopTMVia`. UNIV-1(a) stays an optional generalization.
   Raw-layer exports that move into `Build/Embed` and `Build/Seam` take their host modules'
   universes (`Type*`; MIG-0b round 1, finding 2); the contract structures keep `Type`.
2. **Frames are a derived layer**, not a field. The endpoint already states the frame as
   `{ d with … }`. The layer adds `Cfg.SameOutside` (a per-tape footprint), its composition,
   `.keep` lemmas for stored words and blank tapes, and `Contract.Frames`.

**Compositions, as thin wrappers over the existing rows:**
- `trans`: first-exit sequencing on one machine. It is not a general `RecordRun` concatenation
  (MIG-0a gate, round 1, major; see below);
- `seq`: the R2 seam, time `t₁ + 1 + t₂`;
- `inPhase`: one phase inside the phase host, whose redirect targets lie in other phases (a
  sufficient condition: the run must avoid every redirect target up to its endpoint);
- `embed`: the R1 embedding, with unselected tapes framed and output appended;
- `branch`: the two-way seam;
- `ReturnContract` with `release`: for rows that return to their anchor, whose cut starts at
  time `1`, such as the advancing writer. The install and emit calls quantify separate entry and
  exit states that may coincide, so with arbitrary witnesses they split on `entry = exit`
  (corrected at the gate, round 1, minor 5).

**Fit test.** `trans`, `seq`, `inPhase`, `embed` and `embedEmitCfg_select` are proved with no
statement change and no extra hypothesis, on the standard three axioms. So is the instance
`clearTM_contract`, R3 clear repackaged from `clearTM_run_ofCfg`. A second fit test then
proved the rest: the frames layer (the `SameOutside` lemmas are nearly definitional),
`clearTM_contract_frames` (the footprint is exactly where the endpoint writes blanks), `release`
and `branch`. **The whole MIG-0a draft is proved: 843 lines, 0 errors, 0 warnings**
(`campaign/items/mig0/Contract-draft.lean.txt`).

Further observations from the fit tests:
- **Liveness is a lemma.** A contract's run is live strictly before its time, from the cut and
  `exit_mem`, since a halt would persist to the endpoint. `branch` needs it; promote it as
  `Contract.live`.
- **`branch`'s halting exit is untagged.** If both continuations may halt, a halted endpoint
  does not say which ran. The statement is still correct.
- **A third export:** a pointwise `seamReleaseTM_runFrom_pos`. The release's envelope went
  through `seamReleaseTM_visitedByTapeHead`, because the pointwise lemma is private.
- **Ergonomics:** a `@[simp]` unfolding lemma for `Frames` and `SameOutside`, so that `rw` sees
  a footprint's `if` without a `show`.

The test found two missing public exports, both additive:
- `embedEmitCfg_unselected_tape` and `_pos` (`Build/Embed.lean`). The proof of
  `embedEmitCfg_select` worked around their absence through `embedEmitTM_frame` and a trivial
  machine;
- a right-segment seam lemma (`Build/Seam.lean`), to replace the private `seamComp_right`. It is
  needed for set-valued exits; `seamCompTM_firstReturn_ofCfg` excludes only one target.

**Scope, in two increments:**
- **MIG-0a:** the structure, the derived lemmas, the frames layer, `trans`, `seq`, `inPhase`,
  `embed`, `branch`, `ReturnContract` with `release`, `Contract.live`, and two exports
  (`embedEmitCfg_unselected`, `seamCompTM_runFrom_right`); the pointwise release export is
  deferred to MIG-0b;
- **MIG-0b:** revised after the gate's round 1, below.

**MIG-0a gate, round 1** (2026-10-12: 0 blockers, 1 major, 5 minors; `campaign/gates/04-mig0a/findings.md`,
resolutions `campaign/gates/04-mig0a/resolutions.md`). No proved statement was found false. The major is
about the migration interface: a first-exit `Contract` does not directly replace three kinds of
existing specification, so the direct-replacement claims of MIG-12 and MIG-15 were wrong.
- **Segments.** `CfgRecord`'s `RecordRun` is a fixed-length run that avoids a forbidden verdict
  set; its endpoint need not be a first visit, and `recordRun_trans` concatenates on one machine
  with no dispatch step. The auditor's example: a machine idling at `a` gives a length-2 segment
  from `a` to `a`, which neither a positive `Contract` nor a `ReturnContract` can package.
- **Return-or-escape rounds.** `RecordTable`'s `rt_find_round_entry` and the counter loop's rounds
  end either back at their anchor or at a distinct escape, with positive cuts against both. A
  `Contract` fails its time-zero cut there, and a `ReturnContract` excludes the escape.
- **Joint trajectories.** `CounterLoop`'s `counterSpan` constrains the whole head vector along a
  run. Per-tape intervals cannot express a relation such as "the two heads are equal".

`Contract` stays the first-exit specialization. **MIG-0b** therefore covers, before any
dependent migration:
1. a **segment layer**: fixed-length segments avoiding a forbidden set, with same-machine
   concatenation (the `RecordRun` pattern), and a bridge to `Contract` when the endpoint is a
   first exit;
2. a **round layer**: return-or-escape rounds with positive cuts against the anchor and the
   escape, and the counter loop's composition over them;
3. a **joint-trajectory layer**: a relation on the head vector along the run, derived like
   `Frames` and preserved by the compositions;
4. the **layering split**: a core contract module that `Loop` and `CounterLoop` can import
   (round 1, minor 2), with the adapters and routine instances above it; the two exports move into
   `Build/Embed` and `Build/Seam` then. Round 2's import repair found that the file needs `Seam`,
   `Catalog` and `Mathlib.Tactic.Linarith` (which `CounterLoop` used to supply indirectly), so
   `CounterLoop` is no longer in its closure, but `Loop` still is, through `Catalog`. The core
   part needs only the machine core, apart from `MultiTapeTM.spaceUsedByTape_le_card_Icc`, which
   lives in `Catalog` and moves down first. **Revised by MIG-0b round 2** (2026-10-13;
   `campaign/gates/15-mig0b/pack-r2.md`, NOTES-r2 §3):
   - `spaceUsedByTape_le_card_Icc` and `workTapePos_runFrom_mem_Icc` move to `Finite` (not
     `Deterministic`);
   - `runFrom_mapState_of_agreeOn` moves to `StateRenaming`, which then imports `Simulation`;
   - MIG-0a's private helpers are deleted;
   - `Build/Seam` promotes its polymorphic release and composition lemmas;
   - `AlphabetReduction` imports the core;
   - the Embed exports are stated over `Type*`.

   The core's closure is `Configuration`, `Deterministic`, `Finite`, `Simulation` and
   `StateRenaming`;
5. the pointwise release export `seamReleaseTM_runFrom_pos`;
6. the symbol lift (through `Cfg.decodeSymbols`), state renaming along an embedding
   (`runFrom_mapState_of_agreeOn`), and the alphabet-reduction and robustness-lockstep adapters
   (round 1, note 20);
7. the tactics, and the auditor's suggested sanity lemmas: the zero-time characterization
   (`time = 0 ↔ some entry ∈ exits` on admissible starts) and positivity of the compositions;
8. **the R1 reconstruction lemma** in `Build/Embed`, at the layering split (the wave-1 fill gate's
   major F1, acknowledged by the user): from the selected-bank projections and the unchanged
   ambient frame, equality of an embedded configuration, cited by `OracleSim.oracleBankCfg_eq`,
   `Loop.emCall_exit_fixed`'s local frame and `CodeSimulator.canonEmbedEq`.

MIG-0a's round 2 audits the corrected records and the documentation repairs; no statement or proof
of the file changes. **Round 2 closed the gate** (2026-10-13, 0 blockers / 0 majors / 1 minor;
`campaign/gates/04-mig0a/findings-r2.md`). Its acceptance obligations for MIG-0b's statement gate:
- the segment layer keeps zero-length segments, the inclusive envelope and the actual
  configuration seam (`RecordRun`'s shape);
- `counterSpan` is a segment property (no entry or endpoint constraint; it admits time zero, which
  `counter_rounds` uses), so it migrates to the segment and joint-trajectory layers; positive
  return-or-escape rounds describe the loop body's interface;
- `splitSafe`'s avoidance holds at every time through the endpoint, so it uses the segment layer
  with endpoint-inclusive avoidance, and first-exit `Contract`s apply only where a first exit is
  proved (`SafeRun`, in `Build/EmitIterEmbed.lean`, avoids only strictly before the endpoint: a
  plain segment);
- both round rows also require the round's interior to be live;
- the joint-trajectory property holds for general segments, and keeps the counter loop's single
  shared round and time witness for all body heads, its exact endpoints, bounds and liveness.

**MIG-0b gate, round 1** (2026-10-13; `campaign/gates/15-mig0b/findings.md`): **0 blockers / 2 majors /
4 minors, gate open.** The segment, round and trajectory layers meet round 2's acceptance
obligations above, and no proved statement is false. Both majors concern the landing plan:
- the planned split strands private helpers (`mem_hull_left`, `mem_hull_right`,
  `runFrom_state_none_mono`) and a fit-namespace bridge that kept modules use;
- the release export `seamReleaseTM_runFrom_pos` fixes universes to `Type`, narrower than the
  polymorphic `seamRelease_run_pos` it replaces.

**Round 2 CLOSED the gate** (2026-10-14: 0 blockers / 0 majors / 3 minors;
`campaign/gates/15-mig0b/findings-r2.md`). Round 2 (`campaign/gates/15-mig0b/pack-r2.md`, re-run at `1781a230`): a real
split, cut-checked without the fit namespace; the polymorphic release; and the minors (an
entry-compatibility lemma for `Contract.lockstep`, the release's wording, the alphabet admission's
sketch and reference, and records).

### 16b. Five route decisions (user, 2026-10-12)

The user took the five open route questions together, each as the maintainer recommended (plan
§4e, decision log, 2026-10-12).

**Update (2026-10-14).** Hydroxyi's ARM merge (`8c23f3bc`) proves the customers of items 1
(Savitch at polynomial space), 2 (`TQBF_PSPACEHard`, without RD-2's codec) and 4 (`PATH ∈ NL`,
NL = coNL). The user held RD-2's fills and paused stage 2 (backlog RD-2, PROG-4); general
`savitch` stays open. Item 3's "S1b's private copies re-pointed in the same PR" was carried
out by the B6 hosts' landing (PR #92, merged 2026-10-14): seven private copies removed, five
re-pointed. ConfigGraph's remaining 11 private `s1b_*` declarations have no consumer, and the
payback PR deletes them (backlog §1 ARM-1).

1. **Savitch's space: words of `Θ(S)` bits.** A configuration of the simulated machine is one
   word, so a recursion level holds `O(1)` cells, and depth `O(S)` gives `f = O(S)` cells. Stage
   2's space bound stays cells times word width (§15a), which gives `O(S·(S + log S)) = O(S²)`.
   The alternative, charging each cell for the bits it holds, was declined: every cell still pays
   an `O(log S)`-bit address, so it reaches `O(S²)` only with packing as well. Consequences:
   - **Stage 2 takes a computed word size.** `W` is a function of the input length that the
     compiled machine computes within its space bound: `c·log n` for P and L (from the
     input-length counter, R8.5c) and `c·S(n)` for Savitch (from `S`'s constructibility
     witness).
   - The machine-configuration routines work on packed words, using `half` (PROG-2).
   - With `W = Θ(log n)` and packed configurations, the drafted bound already gives `O(S²)` for
     polynomial `S`. That suffices for `PSPACE = NPSPACE`, but not for `savitch`, which is stated
     for every space-constructible `S`.
2. **B4a is restated in place, over H6.** `exists_adjacency_codec_cnf` becomes public
   definitions of the codec and its three CNFs with closed-form variable indexing, and theorems
   about them in place of the `∃`. Its present formulas index variables through
   `Fintype.equivFin` over types that depend on `n` and `s`, so no machine or program can be
   proved to emit them (Finding A; the `TQBF_PSPACEHard` docstring: "The packaged existential
   supplies no algorithm"). The indexing is designed with H6 (§14), so that Cook–Levin and TQBF
   share one scheme.
   - It changes an audited public statement: a statement gate, then a re-fill. Its only consumer
     is the open `TQBF_PSPACEHard`.
   - Hardness also needs Tseitin on `Std.Sat.CNF ℕ`, correct for every prefix assignment.
   - Whether the `ψᵢ` emitter is a machine (H6) or a program with `emit` is decided with B4
     hardness's design.
   - **Designed (2026-10-12):** `campaign/items/rd2/RD2-design.md`, with a sorried statement draft,
     `campaign/items/rd2/RD2Draft.lean.txt`. The draft elaborates with 0 errors and 36 sorries;
     11 of its theorems are proved. It proposes:
     - the H6 kit as `Complexity.FormulaKit`: block variables, a truth-table gate template with
       closed-form wires, ledgers, and emission over `polyTimeComputable_emitIter`;
     - a generic Tseitin-after-prefix lemma, with its instance for `DAGCircuit.toCNF`;
     - `Complexity.ConfigCodec`: a closed-form layout of width `2n + 4 + Q + 3k(2s + 1)`,
       clause lists ordered by `List.range`, the old statement's clauses as 11 theorems, and new
       uniformity theorems.

     About 820 of the old proof's roughly 1,700 lines survive verbatim (measured at 703 by the
     statement pack's migration list). Estimate: 2.5k–3.6k lines landed; a statement gate, then
     two fills.
   - **Answered (user, 2026-10-12): all five of the note's recommendations.**
     - `exists_adjacency_codec_cnf` is retired; no proof uses it.
     - The uniformity theorems are part of RD-2, as the fill RD-2b.
     - The ψ matrix is a guarded CNF, so the private Tseitin lemmas of the colleague-owned
       `DAGCircuitSat.lean` are not needed.
     - **The ψ emitter is a machine,** on H6 and the polynomial-time closure algebra.
     - The transition gates are truth-table templates, as in Cook–Levin.

     **Statement gate (2026-10-13):** `campaign/gates/11-rd2-statements/pack.md`. The landing form drops the
     Tseitin instance (decision 4), and adds 17 theorems: the kit's cost ledger, so that the
     private twins merge; the fragment and gate emission forms; unary index arithmetic, because
     the codec divides by `2s + 1`; and the port contract. The prefix-truth lemmas are proved.
     **CLOSED** (round 1, 2026-10-14: PASS, 0 blockers / 0 majors / 2 minors;
     `campaign/gates/11-rd2-statements/findings.md`). Next: the landing PR, then RD-2a and RD-2b.
3. **B6 takes the window route, and `space_universal` is restated forward-only.**
   - **The window route.** `space_hierarchy`'s diagonalizer runs one fixed self-simulating
     universal machine `U₀` inside a window of radius `a·g(n)`, on the configuration-record rows,
     stopped by a configuration-count clock, and flips `U₀`'s verdict. It needs `U₀`'s forward
     direction with a space ledger, the windowed runner H3 (record-table rows 17–18, in flight),
     the step block H2 and the native input device of H5. The sketch's budget loop, head caps,
     interval counters and probe/replay go.
   - **Why:** the chapter-1 interpreter cannot serve (Finding B). It tracks the input head in
     unary on its fourth tape, so that tape uses one plus the largest simulated input position
     reached: `Θ(n + 1)` cells on a full scan. So it cannot guarantee `O(S(n))` space uniformly
     for sublinear `S`, which the present sketch's premise needed (wording corrected at the RD-3
     gate, minor 4).
   - **`space_universal` keeps only its forward clause,** as [AB09, Exercise 4.1] states it (p. 93,
     checked 2026-10-12): if `M_α` halts on `x` before using `t` cells of its work tapes, then
     `SU(α, t, x) = M_α(x)`, and `SU` uses at most `C·t` cells. The `[false]` clause goes, and
     with it the interval counters, the core-count clock and the probe/replay. It still needs a
     code-first universal that reads its input through a binary-position device (H5). (Superseded
     2026-10-13: the bounded-prefix ruler device, with `space_universal` at `C·s`; decisions
     B1–B2.)
   - The sketch drops its stale "space-preserving normal form" obligation: the normal form is
     proved (`Turing.FinTM.one_work_tape_binary_spaceUsed`, `Robustness/SingleTape.lean`), but
     two small steps around it were not, and they were fill obligations: the space clause of
     the coding step `exists_codeTM`, which is time-only, and a decider's space bound at every
     time (the normal form needs it at every time; `DecidesInSpace` bounds it at the halt).
     Both are proved in the host draft below.
   - `U₀` and the windowed runner had no statements before the host draft below. `U₀` is a
     public row built from H2 and H5, not a private host of this proof. The runner's contract
     exposes three outcomes (halt, window exit, clock exhaustion). `counterLoopTMVia` has one
     optional early body exit plus clock exhaustion, so H3 can merge halt and window exit into the
     early escape and tell them apart afterwards from the retained record (the RD-3 gate, minor 3).
   - **RD-3's statement gate passed** (2026-10-13, 0 blockers / 0 majors / 4 minors;
     `campaign/gates/05-b6-restatement/findings.md`). `space_universal` keeps its `+ logSpace |x|` addend for
     now; the auditor's addend-free `C·s` route (a bounded-prefix input device, a unary ruler of
     the header's length) is to be decided when H5 is gated.
   - **Host statements drafted (2026-10-13):** `campaign/items/b6hosts/` (design note, and the
     draft `B6HostsDraft.lean.txt`: 0 errors, 10 sorried machine contracts, 43 declarations
     proved). It contains:
     - **H3:** a pure specification `windowRun` with three exits; a step clock shared with C1,
       `exists_stepClockTMVia`; and a clock-agnostic runner for `space_hierarchy`,
       `exists_configWindowRunnerTM`;
     - **H5:** a native device, and a bounded-prefix ruler device with a host transformer;
     - **`U₀`:** a startup, and a forward ledger `C_α·(s + 1)`;
     - **the two fill obligations above, both proved:** `exists_codeTM_spaceUsed` and
       `ComputesInTime.spaceUsed_le_of_halt`.

     Open questions for the user: the note's §10.
   - **Answered (user, 2026-10-13), all as recommended:** `space_universal` is strengthened to the
     book's `C·s` in the B6 hosts' statement-gate pack, through H5's ruler device; no
     binary-position device (its registry row stays); the public `outSummaryCode`/`summaryTag`
     land in `ConfigGraph.lean`, with S1b's private copies re-pointed in the same PR; the
     configuration-count runner and its bound go to a new `SpaceComplexity/WindowClock.lean`, so
     that `Build/WindowRun.lean` imports nothing from `SpaceComplexity`; the contracts are gated
     as `∃` statements, with named machines at fill time.
   - **Statement gate (2026-10-13):** `campaign/gates/13-b6-hosts-statements/pack.md`. Changes from the
     draft:
     - the ruler host is a block simulation (H2-S round 1, finding 2);
     - `U₀`'s sketch uses the reset-output invariant (finding 4);
     - `exists_stepClockTMVia`'s trajectory clause also carries the body tapes, input position and
       output, which the runner's silence and restoration need; C1's form `exists_stepClockTM` is
       unchanged, so C1's pack only re-points its citation at landing;
     - window containment and the B6 summary instance move to `WindowClock`.
   - **CLOSED** (2026-10-14: PASS, 0 blockers / 0 majors / 5 minors;
     `campaign/gates/13-b6-hosts-statements/findings.md`). The step clock keeps `+2`; the runner stays
     clock-agnostic. Next: the landing PR.
   - The shortcut through a space ledger for the time hierarchy's `diagSim` is not taken.
   - The restatement and the re-routed sketches go through a statement gate.
4. **C2 is written as programs with coins.** `PATH ∈ NL`, Immerman–Szelepcsényi and their
   corollaries are programs of the language using read-once `coin` (PROG-2), compiled by stage 2.
   This removes C2's dependency on the nondeterministic `LogProg` extension asked of Hydroxyi
   (plan §2.5; `backlog.md` §2, *ARM extensions*). Stage 2 therefore needs, besides item 1's word
   size:
   - **a nondeterministic form:** each `coin` is one choice step of a `FinNDTM`, with time and
     space bounds uniform over the coin streams (§15c);
   - **a logspace grade:** `O(1)` cells and `W = O(log n)` give space `O(log n)`. This needs the
     input read in place (PROG-2) and the footprint along runs (PROG-3).

   `PATH_NLComplete`'s hardness half needs only the deterministic layer.
5. **§13d G2–G4 stay in the campaign**, after MIG-0b, so that the mapped sweeps, the carrier's
   rows and the rebalance rows are stated as `Contract`s from the start. They share no file with
   stage 2 and can run alongside it. The two open zone rows (`exists_zoneShiftInTM`,
   `exists_zoneShiftOutTM`) retire through the G3/G4 gate, as §13d planned.

**Stage 2's statement** (`backlog.md` PROG-4), drafted together with PROG-2 and PROG-3, therefore
carries a computed word size, deterministic and nondeterministic forms, and a space bound good
enough for L.
````


## ===== lean-toolchain =====

```text
leanprover/lean4:v4.25.0
```


## ===== lakefile.lean =====

```text
import Lake
open Lake DSL

package «tCSlib» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "029db123ddaa"

require PFR from git
  "https://github.com/teorth/pfr.git" @ "e1095d58"

@[default_target]
lean_lib «TCSlib» {
  -- add any library configuration options here
}


meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.25.0"
```


## ===== lake-manifest.json =====

```text
{"version": "1.1.0",
 "packagesDir": ".lake/packages",
 "packages":
 [{"url": "https://github.com/leanprover/doc-gen4",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "0ece4c27ae1abbd0b70df729e09d8b9c06351b80",
   "name": "«doc-gen4»",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.25.0",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/teorth/pfr.git",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "e1095d58b7c6f10734988816f7764f2103b9bf29",
   "name": "PFR",
   "manifestFile": "lake-manifest.json",
   "inputRev": "e1095d58",
   "inherited": false,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/mathlib4.git",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "029db123ddaa",
   "inherited": false,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover/lean4-cli",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "1dae8b12f8ba27576ffe5ddee78bebf6458157b0",
   "name": "Cli",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/fgdorais/lean4-unicode-basic",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "1829aec18f0e8a661dd5acf5d659d636979ba4f2",
   "name": "UnicodeBasic",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/dupuisf/BibtexQuery",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "29a4b34f8caa7c95934ab4494d8866fde1850c0b",
   "name": "BibtexQuery",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/acmepjz/md4lean",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "44da417da3705ede62b5c39382ddd2261ec3933e",
   "name": "MD4Lean",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/YaelDillies/LeanAPAP.git",
   "type": "git",
   "subDir": null,
   "scope": "",
   "rev": "5bbd91f52aa2e2d413a19afc10d30362e4872527",
   "name": "LeanAPAP",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.25.0",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/plausible",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "2503bfb5e2d4d8202165f5bd2cc39e44a3be31c3",
   "name": "plausible",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/LeanSearchClient",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "2ed4ba69b6127de8f5c2af83cccacd3c988b06bf",
   "name": "LeanSearchClient",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/import-graph",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "009064c21bad4d7f421f2901c5e817c8bf3468cb",
   "name": "importGraph",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/ProofWidgets4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "fb8ed0a85a96e3176f6e94b20d413ea72d92576d",
   "name": "proofwidgets",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v0.0.77",
   "inherited": true,
   "configFile": "lakefile.lean"},
  {"url": "https://github.com/leanprover-community/aesop",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "26e4c7c0e63eb3e6cce3cf7faba27b8526ea8349",
   "name": "aesop",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/quote4",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "2781d8ad404303b2fe03710ac7db946ddfe3539f",
   "name": "Qq",
   "manifestFile": "lake-manifest.json",
   "inputRev": "master",
   "inherited": true,
   "configFile": "lakefile.toml"},
  {"url": "https://github.com/leanprover-community/batteries",
   "type": "git",
   "subDir": null,
   "scope": "leanprover-community",
   "rev": "39260e31b7b3f7f05643da95242463b462dc05f1",
   "name": "batteries",
   "manifestFile": "lake-manifest.json",
   "inputRev": "main",
   "inherited": true,
   "configFile": "lakefile.toml"}],
 "name": "tCSlib",
 "lakeDir": ".lake"}
```


## ===== TCSlib.lean =====

```text
import TCSlib.ErrorCorrectingCodes.Basic
import TCSlib.ErrorCorrectingCodes.SingletonBound
import TCSlib.ErrorCorrectingCodes.HammingBound
import TCSlib.ErrorCorrectingCodes.Entropy
import TCSlib.ErrorCorrectingCodes.LinearCodes
import TCSlib.ErrorCorrectingCodes.GilbertVarshamov
import TCSlib.ErrorCorrectingCodes.ListDecoding
import TCSlib.ErrorCorrectingCodes.QuantumSingleton
import TCSlib.ErrorCorrectingCodes.QuantumHamming
import TCSlib.ErrorCorrectingCodes.JohnsonBound
import TCSlib.ErrorCorrectingCodes.MRRW

import TCSlib.BooleanAnalysis.BLR
import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.ArrowTheorem
import TCSlib.BooleanAnalysis.Hypercontractivity
import TCSlib.BooleanAnalysis.GaussianSpace
import TCSlib.BooleanAnalysis.Switching
import TCSlib.BooleanAnalysis.ThresholdFunctions
import TCSlib.BooleanAnalysis.polylogIndep

import TCSlib.CommunicationComplexity.DeterministicCC
import TCSlib.CommunicationComplexity.NewmanTheorem

import TCSlib.Programs

import TCSlib.Complexity.CircuitComplexity
import TCSlib.Complexity.Expanders
import TCSlib.Complexity.NPReductions
import TCSlib.Complexity.Randomized
import TCSlib.Complexity.TuringMachine
import TCSlib.Complexity.Uncomputability
import TCSlib.Complexity.ClassP
import TCSlib.Complexity.Formulas
import TCSlib.Complexity.FormulaKit
import TCSlib.Complexity.CookLevin
import TCSlib.Complexity.RAMSimulation
import TCSlib.Complexity.ClassNP
import TCSlib.Complexity.ClassOracle
import TCSlib.Complexity.Diagonalization
import TCSlib.Complexity.ClassPSPACE
import TCSlib.Complexity.PolyHierarchy
import TCSlib.Complexity.Randomized
import TCSlib.Complexity.TimeHierarchy
import TCSlib.Complexity.SpaceComplexity

import TCSlib.ComputationalModels

import TCSlib.Cryptography.SchnorrProtocol
import TCSlib.Cryptography.SecretSharing
import TCSlib.Cryptography.MPC
import TCSlib.Cryptography.Foundations
import TCSlib.Cryptography.OneWayFunctions
import TCSlib.Cryptography.HardcoreBit
import TCSlib.Cryptography.Pseudorandom
import TCSlib.Cryptography.Asymptotic
import TCSlib.Cryptography.Candidates
import TCSlib.Cryptography.NumberTheory
import TCSlib.Cryptography.Encoding
import TCSlib.Cryptography.LWE
import TCSlib.Cryptography.SIS
import TCSlib.Cryptography.Encryption
import TCSlib.Cryptography.TrapdoorFunctions
import TCSlib.Cryptography.ZeroKnowledge
import TCSlib.Cryptography.Games
import TCSlib.Cryptography.Games.Bridges
import TCSlib.Cryptography.Authentication
import TCSlib.Cryptography.Hashing
import TCSlib.Cryptography.SecureComputation
import TCSlib.Cryptography.Composability
import TCSlib.Cryptography.Encryption.PrivateKey
import TCSlib.Cryptography.Encryption.PublicKey
import TCSlib.Cryptography.Randomness

import TCSlib.InformationTheory

import TCSlib.GraphTheory.Kruskal

import TCSlib.KikuchiLDC.Main

import TCSlib.LearningTheory.MistakeBounds
import TCSlib.LearningTheory.Hedge
import TCSlib.LearningTheory.JohnsonLindenstrauss
import TCSlib.LearningTheory.Minimax
import TCSlib.LearningTheory.PAC
```


## ===== TCSlib/Cryptography/Encryption.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.Symmetric
import TCSlib.Cryptography.Encryption.PublicKey

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic encryption constructions

## Contents

* `Symmetric`: direct symmetric-encryption constructions and concrete experiments.
* `PublicKey`: Regev subset-sum PKE and quantitative concrete security statements.

The machine-valued primitive contracts remain owned by `Cryptography.Asymptotic`.
The construction children state their own proof and implementation status.
-/
```


## ===== TCSlib/Cryptography/Encryption/PublicKey.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.Encryption.PublicKey.HybridMachine
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Candidates.RSA
import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.DDH
import TCSlib.Cryptography.Encryption.PublicKey.ElGamal
import TCSlib.Cryptography.Encryption.PublicKey.Regev
import TCSlib.Cryptography.Composability.PublicKey

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key encryption

## Main definitions

`TCSlib.Cryptography.PublicKeyScheme` and `TCSlib.Cryptography.BitPublicKeyScheme`
give the ensemble interfaces. `TCSlib.Cryptography.Composability.FixedLengthPKScheme`
supports the oracle CPA, CCA1 and CCA2 games.

## Main results

`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme` packages a correct bit scheme.
`TCSlib.Cryptography.TrapdoorCollection.tdpBitScheme_singleBitSecure` proves security
given one-wayness, a hard-core predicate and its efficient evaluator.
`TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` and
`TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` give fixed-vector
multi-message security.

## Contents

* `Scheme` defines the scheme interfaces and their correctness fields.
* `HybridMachine` builds the public-key hybrid reduction and its coin split.
* `Hybrid` proves the shared-key bound on tuples of encryptions.
* `EnsembleSecurity` gives the games, bitwise construction and fixed-vector security theorem.
* `TrapdoorPredictor` builds the machine used to predict the hard-core bit.
* `Trapdoor` proves correctness and single-bit security of Algorithm 104.3 and gives
  the Goldreich–Levin bridge [PS10, §3.10].
* `OracleSecurity` gives the fixed-length scheme, codecs and oracle games [PS10, §7.1.4].
  The proof of `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa` is pending.
* `Composability.PublicKey` re-exports the oracle games and gives the trapdoor CPA corollary.
* `Candidates.RSA` constructs `TCSlib.Cryptography.Candidates.rsaTrapdoor`.
  `TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay` uses
  `TCSlib.Cryptography.Candidates.RSAAssumption`.
* `Candidates.Rabin` constructs `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor`.
  `TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay` uses
  `TCSlib.Cryptography.Candidates.FactoringAssumption` and `TCSlib.Cryptography.Candidates.BlumDensity`.
* `Candidates.DDH` defines the reusable safe-prime DDH assumption.
* `ElGamal` gives the group-message scheme `TCSlib.Cryptography.Candidates.elGamal`.
  `TCSlib.Cryptography.Candidates.elGamal_correct` handles admissible messages.
  `TCSlib.Cryptography.Candidates.elGamal_secure` uses
  `TCSlib.Cryptography.Candidates.DDHAssumption` for `TCSlib.Cryptography.Candidates.egGroupGen`
  and a negligible full-length exception bound for the safe-prime generator.
* `Regev` proves finite subset-sum encryption correctness and an explicit DLWE security bound
  with a leftover-hash error [Pei16, §5.2.1].

The three candidate routes take arithmetic efficiency as
`TCSlib.Cryptography.Candidates.ArithmeticFP`. RSA and Rabin share the trapdoor-bit route.
Its Goldreich–Levin bridge `TCSlib.Cryptography.TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`
requires the encoding-width premise `henc`. ElGamal uses its own group-message game.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016.
-/
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/Regev.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev public-key encryption

## Contents

* `Basic`: mathematical keygen/encryption/decryption and strict bounded-error correctness.
* `Experiments`: explicit DLWE hybrids, binary extraction and quantitative security bounds.

All nontrivial new statements are admitted for the combined statement audit.
The child modules distinguish actual laws and deterministic mathematics from
efficiency/security endpoints. Source-policy work and user-controlled integration
remain open; this facade claims no completed primitive or CCA2 security.
-/
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/Regev/Basic.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.BitEncoding

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev public-key encryption: subset sums and correctness

## Main definitions

* `keygen`: publish the existing LWE sample and retain its one common secret.
* `encrypt`: sum the public samples selected by fresh binary coins, adding a bit codepoint.
* `decrypt`: subtract the secret product and use the existing nearest-codepoint decoder.

## Main results

The residual is the integer subset sum of the original errors plus the codepoint.
The worst-case support bound gives every-coin correctness under an explicit strict
separation condition. These every-coin correctness claims are proved below.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Section 5.2.1 (Regev's LWE cryptosystem).
* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 notes, Lecture 21.

Rows are samples, transposing the presentation in Pei16. The bit codepoint is
`floor(q/2)` and ties decode false. The explicit strict condition below is stronger
than a non-strict quarter-modulus shorthand. This is primal Regev PKE; no lattice
trapdoor, search-LWE reduction, efficient machine or existing primitive bridge is
introduced by these mathematical maps.
-/

namespace TCSlib.Cryptography.Encryption.PublicKey.Regev

open LWE (Parameters Noise)

/-- Generate an LWE public key and retain its single common secret
[Pei16, Section 5.2.1; Wu24, Lecture 21]. -/
def keygen (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) × (Fin P.dimension → ZMod P.modulus) :=
  (LWE.sample P χ r, r.2.1)

/-- The public-key component is exactly the existing common-secret LWE sample. -/
theorem keygen_fst (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (keygen P χ r).1 = LWE.sample P χ r := rfl

/-- The retained secret is the seed's one full uniform secret vector. -/
theorem keygen_snd (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (keygen P χ r).2 = r.2.1 := rfl

/-- Encrypt one bit by a binary subset sum of public samples plus its bit codepoint
[Pei16, Section 5.2.1; Wu24, Lecture 21]. -/
def encrypt (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus :=
  (pk.1.transpose.mulVec (fun i => ((r i).toNat : ZMod P.modulus)),
    (∑ i, pk.2 i * ((r i).toNat : ZMod P.modulus)) + LWE.BitEncoding.codepoint P μ)

/-- The vector component is the transpose matrix times the binary subset vector. -/
theorem encrypt_fst (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    (encrypt P pk μ r).1 =
      pk.1.transpose.mulVec (fun i => ((r i).toNat : ZMod P.modulus)) := rfl

/-- The scalar component is the selected public-value sum plus the message codepoint. -/
theorem encrypt_snd (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    (encrypt P pk μ r).2 =
      (∑ i, pk.2 i * ((r i).toNat : ZMod P.modulus)) + LWE.BitEncoding.codepoint P μ := rfl

/-- Decrypt by subtracting the secret inner product and decoding the resulting residue
[Pei16, Section 5.2.1, specified nearest-codepoint convention]. -/
def decrypt (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (c : (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) : Bool :=
  LWE.BitEncoding.decode P (c.2 - ∑ j, s j * c.1 j)

/-- Decryption reads exactly the scalar residual after the secret product is removed. -/
theorem decrypt_eq (P : Parameters) (s : Fin P.dimension → ZMod P.modulus)
    (c : (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) :
    decrypt P s c = LWE.BitEncoding.decode P (c.2 - ∑ j, s j * c.1 j) := rfl

/-- The decryption residual equals the message codepoint plus the original integer
subset-error sum reduced modulo `q` [Pei16, Section 5.2.1].

**Proof sketch.** Read both encryption projections and `LWE.noisyValues_apply`.
Apply the public dot-product/matrix identity to the common-secret term, distribute
the selected-sample sum, and cancel that term. Integer-cast add/multiply equations
identify the remaining sum without first reducing the errors' signs or magnitudes. -/
theorem encrypt_residual (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ)
    (μ : Bool) (r : Fin P.samples → Bool) :
    (encrypt P (A, LWE.noisyValues P A s e) μ r).2 -
      ∑ j, s j * (encrypt P (A, LWE.noisyValues P A s e) μ r).1 j =
    LWE.BitEncoding.codepoint P μ +
      ((∑ i, e i * ((r i).toNat : ℤ) : ℤ) : ZMod P.modulus) := by
  let v : Fin P.samples → ZMod P.modulus := fun i => ((r i).toNat : ZMod P.modulus)
  have hlin : dotProduct s (A.transpose.mulVec v) = dotProduct (A.mulVec s) v := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have hvalues : LWE.noisyValues P A s e =
      A.mulVec s + fun i => (e i : ZMod P.modulus) := by
    funext i
    rw [LWE.noisyValues_apply]
    rfl
  have herr : dotProduct (fun i => (e i : ZMod P.modulus)) v =
      ((∑ i, e i * ((r i).toNat : ℤ) : ℤ) : ZMod P.modulus) := by
    change (∑ i, (e i : ZMod P.modulus) * ((r i).toNat : ZMod P.modulus)) = _
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  rw [encrypt_snd, encrypt_fst]
  change (dotProduct (LWE.noisyValues P A s e) v + LWE.BitEncoding.codepoint P μ) -
    dotProduct s (A.transpose.mulVec v) = _
  rw [hvalues, add_dotProduct, hlin, herr]
  rw [add_assoc, add_sub_cancel_left, add_comm]

/-- Any binary subset of errors bounded by `B` has absolute sum at most `m*B`
[Pei16, Section 5.2.1, worst-case bounded-support specialization].

**Proof sketch.** Use the shared binary subset-sum bound with the original error
vector and subset coins. -/
theorem subsetError_bound (P : Parameters) (e : Fin P.samples → ℤ)
    (r : Fin P.samples → Bool) (B : ℕ) (he : ∀ i, (e i).natAbs ≤ B) :
    (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤ P.samples * B := by
  exact LWE.binaryErrorSum_bound e r B he

/-- Bounded errors give correctness for every public matrix, secret, bit and subset
coin vector when `2*(m*B) < floor(q/2)` [Pei16, Section 5.2.1, strict refinement].

**Proof sketch.** Substitute `encrypt_residual`, bound the integer subset sum by
`subsetError_bound`, and apply the existing `decode_codepoint_add` theorem. -/
theorem decrypt_encrypt (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ)
    (μ : Bool) (r : Fin P.samples → Bool) (B : ℕ)
    (he : ∀ i, (e i).natAbs ≤ B) (hsep : 2 * (P.samples * B) < P.modulus / 2) :
    decrypt P s (encrypt P (A, LWE.noisyValues P A s e) μ r) = μ := by
  rw [decrypt_eq, encrypt_residual]
  exact LWE.BitEncoding.decode_codepoint_add P (P.samples * B) μ
    (∑ i, e i * ((r i).toNat : ℤ)) (subsetError_bound P e r B he) hsep

/-- Bounded finite-seed noise gives every-keygen-coin and every-encryption-coin
correctness for Regev PKE [Pei16, Section 5.2.1, finite-law specialization].

**Proof sketch.** Read the keygen projections and LWE sampler equation. The noise
support predicate bounds each original row error, so apply `decrypt_encrypt`. -/
theorem decrypt_keygen_encrypt (P : Parameters) (χ : Noise)
    (rg : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins)))
    (μ : Bool) (r : Fin P.samples → Bool) (B : ℕ)
    (hχ : χ.Bounded B) (hsep : 2 * (P.samples * B) < P.modulus / 2) :
    decrypt P (keygen P χ rg).2 (encrypt P (keygen P χ rg).1 μ r) = μ := by
  rw [keygen_snd, keygen_fst]
  have hsample : LWE.sample P χ rg =
      (rg.1, LWE.noisyValues P rg.1 rg.2.1 (fun i => χ.sample (rg.2.2 i))) :=
    Prod.ext (LWE.sample_fst P χ rg) (LWE.sample_snd P χ rg)
  rw [hsample]
  exact decrypt_encrypt P rg.1 rg.2.1 (fun i => χ.sample (rg.2.2 i)) μ r B
    (fun i => (Noise.bounded_iff χ B).mp hχ (rg.2.2 i)) hsep

end TCSlib.Cryptography.Encryption.PublicKey.Regev
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.Regev.Basic
import TCSlib.Cryptography.Hashing.SIS.Universality
import TCSlib.Cryptography.LWE.Experiments
import Mathlib.Data.Fin.Tuple.Basic

import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Regev PKE: explicit concrete security hybrids

## Main definitions

* `view`, `realView`, `uniformKeyView`: publish the key and one encryption.
* `reduction`: a DLWE test that encrypts with independent binary coins.
* `hashParameters`, `augmented`: adapt the existing binary matrix hash to the ciphertext.
* `extractionError`: the explicit strong leftover-hash error.

## Main results

The real-to-uniform-key advantage equals one DLWE advantage. The uniform-key
view is within the leftover-hash error of a fully independent uniform view.
Two fixed bits' real views differ by at most two DLWE advantages plus twice
that extraction error.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Section 5.2.1 (Regev encryption's lossiness hybrids).
* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 notes, Lecture 21.
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

The statements are concrete, fixed-bit indistinguishability claims. Efficient
preprocessing, uniform asymptotic message quantifiers and the existing CPA primitive
bridge remain additional obligations. The reused hash's numeric SIS record is only
a shape adapter; neither SIS hardness nor a bridge between SIS and LWE is used.
-/

namespace TCSlib.Cryptography.Encryption.PublicKey.Regev

open LWE (Parameters Noise)

/-- Publish a public key together with an encryption of a fixed bit
[Pei16, Section 5.2.1, passive-view formulation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def view (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (r : Fin P.samples → Bool) :
    (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) :=
  (pk, encrypt P pk μ r)

/-- The complete view is the original key paired with its subset-sum ciphertext. -/
theorem view_eq (P : Parameters) (μ : Bool)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (r : Fin P.samples → Bool) :
    view P μ pk r = (pk, encrypt P pk μ r) := rfl

/-- The real view uses the actual finite-noise LWE public key and independent
binary encryption coins [Pei16, Section 5.2.1]. -/
@[simps! (config := { isSimp := false }) fst snd]
def realView (P : Parameters) (χ : Noise) (μ : Bool)
    (r : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) ×
        (Fin P.samples → Bool)) :
    (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) :=
  view P μ (LWE.sample P χ r.1) r.2

/-- The real sampler applies `view` to the existing common-secret LWE sample. -/
theorem realView_eq (P : Parameters) (χ : Noise) (μ : Bool)
    (r : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) ×
        (Fin P.samples → Bool)) :
    realView P χ μ r = view P μ (LWE.sample P χ r.1) r.2 := rfl

/-- The first hybrid encrypts under an independently uniform public key
[Pei16, Section 5.2.1]. -/
@[simps! (config := { isSimp := false }) fst snd]
def uniformKeyView (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) × (Fin P.samples → Bool)) :
    (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus) :=
  view P μ r.1 r.2

/-- The uniform-key hybrid applies the same view map to its uniform key seed. -/
theorem uniformKeyView_eq (P : Parameters) (μ : Bool)
    (r : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) × (Fin P.samples → Bool)) :
    uniformKeyView P μ r = view P μ r.1 r.2 := rfl

/-- The DLWE reduction encrypts its fixed bit under the challenge key before running
the view distinguisher [Pei16, Section 5.2.1]. Its subset coins and test coins are separate. -/
def reduction {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) → ρ → Bool)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (r : (Fin P.samples → Bool) × ρ) : Bool :=
  D (view P μ pk r.1) r.2

/-- The reduction calls the original distinguisher on exactly one simulated view. -/
theorem reduction_eq {ρ : Type*} (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) → ρ → Bool)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (r : (Fin P.samples → Bool) × ρ) :
    reduction P μ D pk r = D (view P μ pk r.1) r.2 := rfl

/-- The first hybrid has exactly the DLWE advantage of the encryption reduction
[Pei16, Section 5.2.1].

**Proof sketch.** Reassociate the independent keygen, encryption and distinguisher
seed factors in both experiments. The real side retains the original matrix,
common secret and all row errors; the ideal side retains the full uniform key. -/
theorem real_uniformKey_advantage {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise) (μ : Bool)
    (D : ((Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) → ρ → Bool) :
    distAdv (realView P χ μ) (uniformKeyView P μ) D =
      LWE.decisionAdvantage P χ (reduction P μ D) := by
  let PublicMatrix := Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus)
  let PublicKey := PublicMatrix × (Fin P.samples → ZMod P.modulus)
  let RealSeed := PublicMatrix × ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))
  let SubsetSeed := Fin P.samples → Bool
  have hreal : acceptProb (realView P χ μ) D =
      acceptProb (LWE.sample P χ) (reduction P μ D) := by
    simp only [acceptProb_def, realView_eq, reduction_eq]
    exact uprob_comp_equiv (Equiv.prodAssoc RealSeed SubsetSeed ρ)
      (fun r => D (view P μ (LWE.sample P χ r.1) r.2.1) r.2.2 = true)
  have hkey : acceptProb (uniformKeyView P μ) D =
      acceptProb (id : PublicKey → PublicKey) (reduction P μ D) := by
    simp only [acceptProb_def, uniformKeyView_eq, reduction_eq, id_eq]
    exact uprob_comp_equiv (Equiv.prodAssoc PublicKey SubsetSeed ρ)
      (fun r => D (view P μ r.1 r.2.1) r.2.2 = true)
  rw [LWE.decisionAdvantage_eq, distAdv_def, distAdv_def, hreal, hkey]

/-- Adapt the matrix-hash shape to `n+1` ciphertext coordinates and `m` subset bits.
The norm budget is unused in this unconditional extraction application
[Pei16, Section 5.2.1]. -/
def hashParameters (P : Parameters) : TCSlib.Cryptography.SIS.Parameters where
  dimension := P.dimension + 1
  columns := P.samples
  modulus := P.modulus
  sqNormBound := P.samples
  modulus_ge_two := P.modulus_ge_two

attribute [simps (config := { isSimp := false }) dimension columns modulus sqNormBound]
  hashParameters

/-- Augment the public matrix transpose by its public value vector as the last row
[Pei16, Section 5.2.1, transposed sample convention]. -/
def augmented (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    Matrix (Fin (P.dimension + 1)) (Fin P.samples) (ZMod P.modulus) :=
  Fin.snoc pk.1.transpose pk.2

/-- The augmented matrix consists of the transpose rows followed by the value row. -/
theorem augmented_eq (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    augmented P pk = Fin.snoc pk.1.transpose pk.2 := rfl

/-- Augmentation is a bijection from all public keys to all augmented matrices.

**Proof sketch.** Split the last row from the preceding rows, transpose those
preceding rows back, and apply the public finite-vector snoc equations. -/
theorem augmented_bijective (P : Parameters) : Function.Bijective (augmented P) := by
  let split (A : Matrix (Fin (P.dimension + 1)) (Fin P.samples) (ZMod P.modulus)) :=
    (Matrix.transpose (Fin.init A), A (Fin.last P.dimension))
  have hleft : Function.LeftInverse split (augmented P) := by
    intro pk
    simp only [split, augmented_eq, Fin.init_snoc, Fin.snoc_last, Matrix.transpose_transpose]
  have hright : Function.RightInverse split (augmented P) := by
    intro A
    simp only [split, augmented_eq, Matrix.transpose_transpose, Fin.snoc_init_self]
  exact ⟨hleft.injective, hright.surjective⟩

/-- The ciphertext is the existing binary matrix hash plus a last-coordinate message
translation [Pei16, Section 5.2.1].

**Proof sketch.** Read the two encryption projections, the augmented matrix equation
and the existing `Hashing.SIS.hash_eq`. Each preceding coordinate is the selected
matrix-column sum; the last coordinate is the selected value sum plus the codepoint. -/
theorem encrypt_augmented (P : Parameters)
    (pk : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) (μ : Bool) (r : Fin P.samples → Bool) :
    let hashed : Fin (P.dimension + 1) → ZMod P.modulus :=
      Hashing.SIS.hash (hashParameters P) (augmented P pk) r
    Fin.snoc (α := fun _ : Fin (P.dimension + 1) => ZMod P.modulus)
      (encrypt P pk μ r).1 (encrypt P pk μ r).2 =
      hashed +
        Fin.snoc (α := fun _ : Fin (P.dimension + 1) => ZMod P.modulus)
          (0 : Fin P.dimension → ZMod P.modulus) (LWE.BitEncoding.codepoint P μ) := by
  dsimp only
  rw [Hashing.SIS.hash_eq, augmented_eq, encrypt_fst, encrypt_snd]
  let v : Fin P.samples → ZMod P.modulus := fun j => ((r j).toNat : ZMod P.modulus)
  let rows : Matrix (Fin (P.dimension + 1)) (Fin P.samples) (ZMod P.modulus) :=
    Fin.snoc pk.1.transpose pk.2
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp only [Pi.add_apply, Fin.snoc_last]
    change (∑ j, pk.2 j * v j) + LWE.BitEncoding.codepoint P μ =
      (∑ j, rows (Fin.last P.dimension) j * v j) + LWE.BitEncoding.codepoint P μ
    simp only [rows, Fin.snoc_last]
  · intro j
    simp only [Pi.add_apply, Fin.snoc_castSucc, Pi.zero_apply, add_zero]
    change dotProduct (pk.1.transpose j) v = dotProduct (rows j.castSucc) v
    simp only [rows, Fin.snoc_castSucc]

/-- The explicit strong-extraction error is half the square root of
`q^(n+1)/2^m` [Pei16, Section 5.2.1; Vad12, Theorem 6.18]. -/
noncomputable def extractionError (P : Parameters) : ℝ :=
  (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ (P.dimension + 1) / (2 : ℝ) ^ P.samples)

/-- The error includes the additional public-value coordinate as well as the matrix
coordinates; its denominator is the cardinality of the binary subset coins. -/
theorem extractionError_eq (P : Parameters) :
    extractionError P =
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ (P.dimension + 1) / (2 : ℝ) ^ P.samples) := rfl

/-- The uniform-key encryption view is within `extractionError P` of a fully uniform,
independent public-key/ciphertext pair [Pei16, Section 5.2.1].

**Proof sketch.** Relabel the key seed by augmentation. Translate the hash output
by the message codepoint and invert finite-vector snoc to recover the ciphertext.
The ciphertext identity gives the same real acceptance probability after this
relabeling. The same output bijection preserves uniformity of the ideal pair.
Apply the strong leftover-hash advantage bound to the resulting test. -/
theorem uniformKey_uniform_advantage_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (μ : Bool)
    (D : ((Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) → ρ → Bool) :
    distAdv (uniformKeyView P μ)
      (id : ((Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → ZMod P.modulus)) ×
        ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) → _) D ≤
      extractionError P := by
  let Key := Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    (Fin P.samples → ZMod P.modulus)
  let AugKey := Matrix (Fin (P.dimension + 1)) (Fin P.samples) (ZMod P.modulus)
  let Ciphertext := (Fin P.dimension → ZMod P.modulus) × ZMod P.modulus
  let Output := Fin (P.dimension + 1) → ZMod P.modulus
  let Input := Fin P.samples → Bool
  let keyEquiv : Key ≃ AugKey := Equiv.ofBijective (augmented P) (augmented_bijective P)
  let cipherEquiv : Ciphertext ≃ Output :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => ZMod P.modulus))
  let shift : Output :=
    Fin.snoc (0 : Fin P.dimension → ZMod P.modulus) (LWE.BitEncoding.codepoint P μ)
  let unpack : AugKey × Output ≃ Key × Ciphertext :=
    keyEquiv.symm.prodCongr ((Equiv.addRight shift).trans cipherEquiv.symm)
  let keySeeds : Key × Input ≃ AugKey × Input := keyEquiv.prodCongr (Equiv.refl Input)
  let sampleHash (r : AugKey × Input) : AugKey × Output :=
    (r.1, Hashing.SIS.hash (hashParameters P) r.1 r.2)
  let test (v : AugKey × Output) (coins : ρ) : Bool := D (unpack v) coins
  have hsampler : uniformKeyView P μ = fun r => unpack (sampleHash (keySeeds r)) := by
    funext r
    rw [uniformKeyView_eq, view_eq]
    have hcipher : cipherEquiv (encrypt P r.1 μ r.2) =
        (sampleHash (keySeeds r)).2 + shift :=
      encrypt_augmented P r.1 μ r.2
    change (r.1, encrypt P r.1 μ r.2) =
      (keyEquiv.symm (keyEquiv r.1),
        cipherEquiv.symm ((sampleHash (keySeeds r)).2 + shift))
    rw [Equiv.symm_apply_apply, ← hcipher, Equiv.symm_apply_apply]
  have hreal : acceptProb (uniformKeyView P μ) D = acceptProb sampleHash test := by
    rw [hsampler]
    simpa only [acceptProb_def] using
      acceptProb_comp_equiv keySeeds (fun r => unpack (sampleHash r)) D
  have hideal : acceptProb (id : Key × Ciphertext → Key × Ciphertext) D =
      acceptProb (id : AugKey × Output → AugKey × Output) test := by
    simpa only [acceptProb_def, id_eq] using
      (acceptProb_comp_equiv unpack (id : Key × Ciphertext → Key × Ciphertext) D).symm
  have hbound := Hashing.SIS.distAdv_hash_uniform_le (hashParameters P) test
  rw [distAdv_def] at hbound ⊢
  rw [hreal, hideal, extractionError_eq]
  simpa only [hashParameters_modulus, hashParameters_dimension, hashParameters_columns] using hbound

/-- Two fixed bits' real encryption views differ by at most two DLWE advantages
plus twice the explicit leftover-hash error [Pei16, Section 5.2.1, quantitative form].

**Proof sketch.** Insert each uniform-key view and a common fully independent
uniform view between the two real views. The real absolute-value triangle
inequality gives two exact DLWE terms and two extraction errors. This uses one
common-secret DLWE instance with exactly `P.samples` rows, not a stronger oracle. -/
theorem distAdv_encrypt_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (χ : Noise) (μ₀ μ₁ : Bool)
    (D : ((Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) ×
      ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)) → ρ → Bool) :
    distAdv (realView P χ μ₀) (realView P χ μ₁) D ≤
      LWE.decisionAdvantage P χ (reduction P μ₀ D) +
      LWE.decisionAdvantage P χ (reduction P μ₁ D) + 2 * extractionError P := by
  let View := (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
    (Fin P.samples → ZMod P.modulus)) × ((Fin P.dimension → ZMod P.modulus) × ZMod P.modulus)
  let ideal : View → View := id
  have hkey₀ := real_uniformKey_advantage P χ μ₀ D
  have hkey₁ := real_uniformKey_advantage P χ μ₁ D
  have hstat₀ : distAdv (uniformKeyView P μ₀) ideal D ≤ extractionError P :=
    uniformKey_uniform_advantage_le P μ₀ D
  have hstat₁ : distAdv (uniformKeyView P μ₁) ideal D ≤ extractionError P :=
    uniformKey_uniform_advantage_le P μ₁ D
  have htriangle₀ := abs_sub_le (acceptProb (realView P χ μ₀) D)
    (acceptProb (uniformKeyView P μ₀) D) (acceptProb (realView P χ μ₁) D)
  have htriangle₁ := abs_sub_le (acceptProb (uniformKeyView P μ₀) D)
    (acceptProb ideal D) (acceptProb (realView P χ μ₁) D)
  have htriangle₂ := abs_sub_le (acceptProb ideal D)
    (acceptProb (uniformKeyView P μ₁) D) (acceptProb (realView P χ μ₁) D)
  rw [abs_sub_comm (acceptProb ideal D) (acceptProb (uniformKeyView P μ₁) D),
    abs_sub_comm (acceptProb (uniformKeyView P μ₁) D) (acceptProb (realView P χ μ₁) D)] at htriangle₂
  rw [distAdv_def] at hkey₀ hkey₁ hstat₀ hstat₁ ⊢
  linarith only [hkey₀, hkey₁, hstat₀, hstat₁, htriangle₀, htriangle₁, htriangle₂]

/-- A width bound and `2κ` sample slack make twice the extraction error at most
`2^(-κ)` [Pei16, Section 5.2.1, explicit sufficient parameter budget].

**Proof sketch.** Apply `Hashing.SIS.leftover_error_le` at the augmented hash
parameters, then multiply its half-error bound by two. -/
theorem two_extractionError_le (P : Parameters) (width κ : ℕ)
    (hq : P.modulus ≤ 2 ^ width)
    (hm : (P.dimension + 1) * width + 2 * κ ≤ P.samples) :
    2 * extractionError P ≤ ((2 : ℝ)⁻¹) ^ κ := by
  have h := Hashing.SIS.leftover_error_le (hashParameters P) width κ
    (by simpa only [hashParameters_modulus] using hq)
    (by simpa only [hashParameters_dimension, hashParameters_columns] using hm)
  rw [hashParameters_modulus, hashParameters_dimension, hashParameters_columns] at h
  rw [extractionError_eq]
  linarith only [h]

end TCSlib.Cryptography.Encryption.PublicKey.Regev
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/Scheme.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Public-key encryption schemes

## Main definitions

* `TCSlib.Cryptography.PublicKeyScheme` is the scheme interface for `n`-bit messages.
* `TCSlib.Cryptography.BitPublicKeyScheme` is the interface for a single-bit message.

## Main results

Each `correct` field requires decryption to recover the message for every choice of
key-generation and encryption coins.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 102.1 and Algorithm 104.3.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-- A **public-key encryption scheme** [PS10, Definition 102.1]: a PPT key generator
`Gen(1^n) = ⟨pk, sk⟩`, a PPT encryptor `Enc_pk(m)` for `m ∈ {0,1}^n` (activated on `⟨pk, m⟩`),
a deterministic polynomial-time decryptor `Dec_sk(c)` (applied to `⟨sk, c⟩`, output decoded as an
`n`-bit string, `⊥` = any other output), with perfect correctness (clause (5)) for every coin
string.

**Deviation:** `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the
canonical message. -/
structure PublicKeyScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(m)`, activated on `⟨pk, m⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness [PS10, Definition 102.1 (5)]. -/
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m

/-- A **single-bit public-key encryption scheme**: [PS10, Definition 102.1] with message space
`{0,1}` (the message `b` is the string `[b]`), as used in [PS10, p. 103 and Algorithm 104.3]. The
components and the conventions are those of `PublicKeyScheme`; correctness is `Dec_sk(Enc_pk(b)) = [b]`
for every coin string. -/
structure BitPublicKeyScheme where
  /-- The key generator `Gen(1^n) = ⟨pk, sk⟩`. -/
  gen : NUPPT
  /-- The encryptor `Enc_pk(b)`, activated on `⟨pk, [b]⟩`. -/
  enc : NUPPT
  /-- The deterministic decryptor on `⟨sk, c⟩`. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness on both bits, for every coin string. -/
  correct : ∀ n (b : Bool) (rg : gen.Coins n) (re : enc.Coins n),
    dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) [b]) re)) = [b]

end TCSlib.Cryptography
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/EnsembleSecurity.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Encryption.PublicKey.Scheme
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Ensemble security for public-key encryption

The experiments expose the public key with the ciphertexts. In the fixed-vector
experiment, all encryptions share one key and use independent encryption coins.

The scheme interface gives decryption the secret key and ciphertext. A scheme
that needs `1^n` for decryption includes it in the secret key.

## Main definitions

* `TCSlib.Cryptography.PublicKeyScheme.pkEncDist` and `PublicKeyScheme.Secure` give the
  single-message experiment and security predicate.
* `TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist` and
  `PublicKeyScheme.MultiMessageSecure` give the fixed-vector experiment and security predicate.
* `TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist` and `BitPublicKeyScheme.SingleBitSecure`
  specialize the experiment to one bit. `BitPublicKeyScheme.bitwise` encrypts a string bit by bit.
* `TCSlib.Cryptography.hybridPlant` inserts a challenge ciphertext at the selected position
  and encrypts the other messages with the public key.

## Main results

* `TCSlib.Cryptography.distAdv_multi_le_sum` bounds the fixed-vector advantage by the sum
  of the single-position advantages.
* `TCSlib.Cryptography.PublicKeyScheme.Secure.multiMessageSecure` lifts single-message
  security to fixed-vector security.
* `TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise` proves security of
  the bitwise scheme. `BitPublicKeyScheme.singleBitSecure_iff` characterizes single-bit
  security by the negligible advantage between the two possible messages.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 102.2 and p. 103.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset
open PrivateKeyScheme (encodeList)

/-! ## Ensemble security [PS10, Definition 102.2] -/

namespace PublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(m)⟩}` of [PS10, Definition 102.2] as a
sampler from the coins of `Gen` and `Enc`. -/
def pkEncDist (S : PublicKeyScheme) (n : ℕ) (m : Fin n → Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn m)) r.2)

/-- **Secure public-key encryption** [PS10, Definition 102.2]: for every non-uniform PPT `D`
there is a negligible `ε` such that for all `n` and `m₀, m₁ ∈ {0,1}^n`, `D` distinguishes
`⟨pk, Enc_pk(m₀)⟩` from `⟨pk, Enc_pk(m₁)⟩` with advantage at most `ε(n)`.

**Deviation:** `D` receives `1^n` with its sample (D5). -/
def Secure (S : PublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool),
    distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

namespace PublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, ⟨Enc_pk(m₀), …, Enc_pk(m_q)⟩⟩}` of the
multi-message security notion for public-key encryption [PS10, p. 103]: `q + 1` encryptions
under one public key with independent encryption coins. -/
def pkMultiEncDist (S : PublicKeyScheme) (n q : ℕ) (m : Fin (q + 1) → Fin n → Bool) :
    S.gen.Coins n × (Fin (q + 1) → S.enc.Coins n) → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1)) (encodeList (List.ofFn fun i =>
    S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) (List.ofFn (m i))) (r.2 i)))

/-- **Multi-message secure public-key encryption** [PS10, p. 103, "we can extend the
definition to multi-message security", i.e. Definition 93.1 with a public key]: for every
non-uniform PPT `D` and polynomial `q` there is a negligible `ε` such that for all `n` and all
message vectors `m, m' ∈ ({0,1}^n)^{q(n)+1}`, `D` distinguishes the encryptions of `m` from
those of `m'` under one key pair with advantage at most `ε(n)` (the public key is part of the
sample).

**Deviation:** `D` receives `1^n`; the ciphertexts are nested pairs. -/
def MultiMessageSecure (S : PublicKeyScheme) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
      distAdv (S.pkMultiEncDist n (q.eval n) m) (S.pkMultiEncDist n (q.eval n) m')
        (D.distinguisherL n) ≤ ε n

end PublicKeyScheme

/-! ## The shared-key hybrid lemma (Thm-103.d, concrete) -/

/-- The `j`-th hybrid distinguisher of the single ⇒ multi-message argument
[PS10, p. 103, "the key point here is that we can efficiently generate encryptions of any
message, without knowing the secret key"]: on a sample `⟨pk, c⟩` it encrypts `m'_0, …, m'_{j-1}`
and `m_{j+1}, …, m_q` itself under `pk` with its own coins `r.1`, plants `c` at position `j`
and runs `D` with coins `r.2`. -/
def hybridPlant {π μ γ ρ ρ' : Type*} {q : ℕ} (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (j : Fin (q + 1)) (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    π × γ → (Fin (q + 1) → ρ) × ρ' → Bool :=
  fun pc r => D (pc.1, fun i =>
    if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i)) r.2

/-- **The hybrid bound with a shared public parameter** (the concrete content of the single ⇒
multi-message theorem for public-key encryption [PS10, p. 103] and of the multi-value hiding of
commitments [PS10, Theorem 126.4, "show this!"]): for a parameter sampler `P` (the public key
from `Gen`'s coins), an encryptor `E pk m r`, message vectors `m, m'` and any `D`, the advantage
of `D` between the `q + 1` encryptions of `m` and of `m'` under one `pk` is at most the sum over
`j` of the advantages of `hybridPlant E m m' j D` between the single encryptions of `m_j` and
`m'_j`. (Unlike `exists_multicopyRed_ge` the copies share the parameter `pk` and the samplers
depend on the position.)

**Proof sketch.** Hybrids `H_j := ⟨pk, (E pk m'_i r_i)_{i<j}, (E pk m_i r_i)_{i≥j}⟩` on the seeds
`κ × (Fin (q+1) → ρ)`, `H_0` and `H_{q+1}` the two sides; `abs_sub_le_sum_hybrids` over
`j ∈ range (q+1)` (`Fin.sum_univ_eq_sum_range`). Each gap `|Pr[D(H_j)] − Pr[D(H_{j+1})]|` equals
the advantage of `hybridPlant E m m' j D` between `⟨pk, E pk m_j r⟩` and `⟨pk, E pk m'_j r⟩`:
`acceptProb (⟨pk, E pk m_j r⟩) (hybridPlant …)` is the probability over `(k, r), (v, r')` of
`D ⟨P k, plant_j (E (P k) m_j r) v⟩ r'`, in which the coordinate `v j` is unused; replacing
`v` by `update v j r` (`OneWay.uprob_update`, `[Nonempty ρ]`) and regrouping the seeds
(`uprob_comp_equiv`) gives `Pr[D(H_j)]`, and likewise `m'_j` gives `Pr[D(H_{j+1})]`
(`Function.update_apply`, the `if` cases `i < j`, `i = j`, `i > j`). -/
theorem distAdv_multi_le_sum {κ π μ γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D ≤
    ∑ j : Fin (q + 1), distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
      (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2)) (hybridPlant E m m' j D) :=
  distAdv_tuple_le_sum P E m m' D

/-! ## Single-bit security and the bitwise scheme [PS10, p. 103] -/

namespace BitPublicKeyScheme

/-- The distribution `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc_pk(b)⟩}` of a single-bit scheme. -/
def pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.gen.Coins n × S.enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (S.gen.runAt n [] r.1))
    (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2)

/-- The single-bit sampler returns the public key and the encryption of `[b]`
on the supplied key-generation and encryption coins. -/
theorem pkEncDist_eq (S : BitPublicKeyScheme) (n : ℕ) (b : Bool)
    (r : S.gen.Coins n × S.enc.Coins n) :
    S.pkEncDist n b r = pairEncode (pairFstD (S.gen.runAt n [] r.1))
      (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] r.1)) [b]) r.2) := rfl

/-- **Single-bit security** [PS10, p. 103, "we only require that encryptions of 0 and 1 are
indistinguishable"]: Definition 102.2 with message space `{0,1}`: for every non-uniform PPT `D`
there is a negligible `ε` with, for all `n` and `b₀, b₁ ∈ {0,1}`, advantage at most `ε(n)`
between `⟨pk, Enc_pk(b₀)⟩` and `⟨pk, Enc_pk(b₁)⟩`. -/
def SingleBitSecure (S : BitPublicKeyScheme) : Prop :=
  ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n (b₀ b₁ : Bool),
    distAdv (S.pkEncDist n b₀) (S.pkEncDist n b₁) (D.distinguisherL n) ≤ ε n

/-- **Single-bit security is the negligibility of the `0`-versus-`1` advantage** (the only
nontrivial pair of messages; sanity for the quantifier form of the definition).

**Proof sketch.** `→`: specialize to `(false, true)` and `Negligible.mono` (the advantage is
nonnegative). `←`: take `ε n` to be the `(false, true)` advantage itself; the pairs `(b, b)` have
advantage `0` and `(true, false)` the same advantage (`abs_sub_comm`). -/
theorem singleBitSecure_iff (S : BitPublicKeyScheme) : S.SingleBitSecure ↔
    ∀ D : NUPPT, Negligible fun n =>
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) := by
  constructor
  · intro h D
    obtain ⟨ε, hε, hle⟩ := h D
    refine hε.mono ⟨0, fun n _ => ?_⟩
    have h0 : 0 ≤ distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) :=
      abs_nonneg _
    rw [abs_of_nonneg h0]
    exact (hle n false true).trans (le_abs_self _)
  · intro h D
    refine ⟨_, h D, fun n b₀ b₁ => ?_⟩
    cases b₀ <;> cases b₁
    · simp only [distAdv_def, sub_self, abs_zero]; exact abs_nonneg _
    · exact le_rfl
    · exact (abs_sub_comm _ _).le
    · simp only [distAdv_def, sub_self, abs_zero]; exact abs_nonneg _

/-- The raw encryptor of the bitwise scheme on the layout `⟨⟨⟨1^n, ⟨pk, m⟩⟩, []⟩, r⟩`: the block
encryptor with one-bit blocks on the state `⟨1^n, ⟨pk, ⟨m, r⟩⟩⟩`. -/
def bitwiseEncFun (S : BitPublicKeyScheme) (z : List Bool) : List Bool :=
  blockEncFun S.enc.output (.const 1) S.enc.coins
    (blockState (NUPPT.inParam z) (pairFstD (NUPPT.inArg z)) (pairSndD (NUPPT.inArg z))
      (NUPPT.inCoins z))

/-- The raw encryptor of the bitwise scheme is polynomial-time. -/
theorem bitwiseEncFun_poly (S : BitPublicKeyScheme) : PolyTimeComputable S.bitwiseEncFun :=
  (blockEncFun_poly S.enc.polyTimeComputable_output _ _).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
        ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode
          NUPPT.polyTimeComputable_inCoins)))

/-- A string of the right length is the encoding of a typed string. -/
private theorem exists_ofFn_eq {ℓ : ℕ} (w : List Bool) (h : w.length = ℓ) :
    ∃ x : Fin ℓ → Bool, List.ofFn x = w := by
  subst h
  exact ⟨fun j => w.get j, List.ofFn_get w⟩

/-- A `flatMap` of singletons indexed by `Fin n` is the string. -/
private theorem flatMap_ofFn_singleton {n : ℕ} (f : Fin n → List Bool) (g : List Bool → List Bool)
    (m : Fin n → Bool) (h : ∀ i, g (f i) = [m i]) :
    (List.ofFn f).flatMap g = List.ofFn m := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.flatMap_cons, h, ih (fun i => f i.succ) (fun i => m i.succ)
      (fun i => h i.succ)]
    rfl

/-- **Unfolding of the bitwise encryptor**: `Enc'(1^n, ⟨pk, m⟩; r)` is the tuple of the `n`
single-bit encryptions `Enc(1^n, ⟨pk, [m_i]⟩; r_i)` with the consecutive `B(n)`-coin segments
`r_i` of `r` (`blockEncFun_spec`, `blockList_ofFn`, `Uniform.runAtL_eq`). -/
theorem bitwise_enc_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool) (m : Fin n → Bool)
    (r : List Bool) :
    (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAtL n
        (pairEncode pk (List.ofFn m)) r =
      encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
  rw [NUPPT.runAtL_ofPolyTimeUniform]
  simp only [bitwiseEncFun, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, blockEncFun_eq]
  rw [blockEncFun_spec S.enc.output (.const 1) S.enc.coins (List.replicate n true) pk
    _ (List.ofFn m) r (by
      simp only [blockState_eq, length_pairEncode, List.length_ofFn, PolyExpr.eval_const, mul_one]
      omega)]
  simp only [PolyExpr.eval_const, List.length_replicate]
  rw [blockList_ofFn S.enc.output _ _ _ n m r _ (by
    simp only [blockState_eq, length_pairEncode, List.length_ofFn]; omega)]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  rw [S.enc_uniform.runAtL_eq]
  rfl

/-- **Unfolding of the bitwise encryptor**, typed coins: `Enc'(1^n, ⟨pk, m⟩; r)` is the tuple of
the single-bit encryptions with the consecutive `B(n)`-coin segments of `List.ofFn r`. -/
theorem bitwise_enc_runAt (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool) (m : Fin n → Bool)
    (r : (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).Coins n) :
    (NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode pk (List.ofFn m)) r =
      encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i (List.ofFn r))) := by
  rw [NUPPT.runAt_eq, bitwise_enc_runAtL]

/-- **The bitwise scheme** [PS10, p. 103, "simply encrypting each bit of the message using the
single-bit secure encryption"]: the same key generator, `Enc'_pk(m) = ⟨Enc_pk(m_1), …, Enc_pk(m_n)⟩`
with `n · B(n)` coins (`blockEncFun`, one-bit blocks), `Dec'_sk(c) = Dec_sk(c_1) ‖ ⋯ ‖ Dec_sk(c_n)`
(`decListFun`), decoded as an `n`-bit string.

**Deviation:** the text's "`Dec` returns `⊥` if any bit decrypts to `⊥`" is realised only up
to the output-length convention of D5 (an honest ciphertext decrypts correctly; a malformed one
decrypts to a wrong-length string or to an arbitrary `n`-bit string). -/
noncomputable def bitwise (S : BitPublicKeyScheme) : PublicKeyScheme where
  gen := S.gen
  enc := NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)
  dec := decListFun S.dec
  gen_uniform := S.gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := decListFun_poly S.dec_poly
  correct := by
    intro n m rg re
    rw [bitwise_enc_runAt, decListFun_eq,
      decListFun_spec S.dec _ _ _ (by
        refine (length_le_length_encodeList _).trans ?_
        simp only [length_pairEncode]
        omega)]
    rw [flatMap_ofFn_singleton _ _ m (fun i => ?_)]
    · exact decodeFin_ofFn m
    · have hre : (List.ofFn re).length = n * S.enc.coins.eval n := by
        rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn S.bitwiseEncFun_poly (.mul .var S.enc.coins)
          n re, List.length_ofFn, PolyExpr.eval_mul, PolyExpr.eval_var]
      have hlen : (coinBlock (S.enc.coinLen n) i (List.ofFn re)).length = S.enc.coinLen n := by
        simp only [coinBlock_eq, List.length_take, List.length_drop]
        rw [hre, NUPPT.coinLen_eq]
        have hi : (i : ℕ) + 1 ≤ n := i.isLt
        have := Nat.mul_le_mul_right (S.enc.coins.eval n) hi
        rw [Nat.add_mul, one_mul] at this
        omega
      obtain ⟨re', hre'⟩ := exists_ofFn_eq _ hlen
      have := S.correct n (m i) rg re'
      rw [NUPPT.runAt_eq (A := S.enc), hre'] at this
      exact this

/-- The coin count of the bitwise encryptor: `n · B(n)`. -/
theorem bitwise_enc_coinLen (S : BitPublicKeyScheme) (n : ℕ) :
    n * S.enc.coinLen n = (PolyExpr.mul .var S.enc.coins).eval n := by
  rw [NUPPT.coinLen_eq, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- **The coins of the bitwise encryptor are `n` single-bit coin blocks**: the published
equivalence `(Fin n → {0,1}^{B(n)}) ≃ S.bitwise.enc.Coins n` (`coinBlocks`, then `finCongr` along
`bitwise_enc_coinLen` and the coin equivalence of `ofPolyTimeUniform`). -/
noncomputable def bitwiseEncCoins (S : BitPublicKeyScheme) (n : ℕ) :
    (Fin n → S.enc.Coins n) ≃ S.bitwise.enc.Coins n :=
  (coinBlocks n (S.enc.coinLen n)).trans
    ((Equiv.arrowCongr (finCongr (S.bitwise_enc_coinLen n)) (Equiv.refl Bool)).trans
      (NUPPT.coinsEquiv_ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins) n).symm)

/-- The bitwise encryptor's coin string on the blocks `v` is that of `coinBlocks n B v`. -/
theorem bitwiseEncCoins_ofFn (S : BitPublicKeyScheme) (n : ℕ) (v : Fin n → S.enc.Coins n) :
    List.ofFn (S.bitwiseEncCoins n v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) := by
  have key : ∀ w, List.ofFn ((NUPPT.coinsEquiv_ofPolyTimeUniform S.bitwiseEncFun_poly
      (.mul .var S.enc.coins) n).symm w) = List.ofFn w := fun w => by
    rw [← NUPPT.coinsEquiv_ofPolyTimeUniform_ofFn, Equiv.apply_symm_apply]
  unfold bitwiseEncCoins
  rw [Equiv.trans_apply, Equiv.trans_apply]
  exact (key _).trans (List.ofFn_congr (S.bitwise_enc_coinLen n) _).symm

/-- The single-bit sampler is `singleDist` on the one-bit message `[b]`. -/
private theorem pkEncDist_eq_singleDist (S : BitPublicKeyScheme) (n : ℕ) (b : Bool) :
    S.pkEncDist n b = singleDist S.gen S.enc n 1 (fun _ => b) := by
  funext r
  simp only [BitPublicKeyScheme.pkEncDist, singleDist_def, ofFn_fin_one]

/-- The ciphertext of the bitwise scheme on the coin blocks `v` is the tuple of the single-bit
encryptions with coins `v_i` (`bitwise_enc_runAt`, `coinBlock_ofFn_coinBlocks`): the sampler
`S.bitwise.pkEncDist n m` read through `bitwiseEncCoins` is `multiDist` with one-bit blocks. -/
private theorem bitwise_pkEncDist_coinBlocks (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    (r : S.gen.Coins n) (v : Fin n → S.enc.Coins n) :
    S.bitwise.pkEncDist n m (r, S.bitwiseEncCoins n v) =
      multiDist S.gen S.enc n n 1 (fun i _ => m i) (r, v) := by
  show pairEncode (pairFstD (S.gen.runAt n [] r))
      ((NUPPT.ofPolyTimeUniform S.bitwiseEncFun_poly (.mul .var S.enc.coins)).runAt n
        (pairEncode (pairFstD (S.gen.runAt n [] r)) (List.ofFn m)) (S.bitwiseEncCoins n v)) =
    _
  rw [bitwise_enc_runAt]
  simp only [multiDist_eq]
  refine congrArg _ (congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_))
  rw [bitwiseEncCoins_ofFn, coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq, ofFn_fin_one]

/-- **The bitwise scheme's ciphertexts as a tuple of single-bit encryptions**: the acceptance
probability of any distinguisher on `S.bitwise.pkEncDist n m` is its acceptance probability on
`multiDist` with one-bit blocks (the coin bijection `coinBlocks`, `uprob_comp_equiv`). -/
private theorem acceptProb_bitwise_pkEncDist (S : BitPublicKeyScheme) (n : ℕ) (m : Fin n → Bool)
    {ρ : Type*} [Fintype ρ] (Dst : List Bool → ρ → Bool) :
    acceptProb (S.bitwise.pkEncDist n m) Dst =
      acceptProb (multiDist S.gen S.enc n n 1 (fun i _ => m i)) Dst := by
  rw [acceptProb_def, acceptProb_def]
  rw [← uprob_comp_equiv
    (((Equiv.refl (S.gen.Coins n)).prodCongr (S.bitwiseEncCoins n)).prodCongr
      (Equiv.refl ρ))]
  congr 1
  funext z
  obtain ⟨⟨r, v⟩, ρ'⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.refl_apply]
  rw [bitwise_pkEncDist_coinBlocks]

/-- **Bitwise encryption under a single-bit secure scheme is secure** [PS10, p. 103, "the security
of the new scheme follows directly from the multi-message security (which is equivalent to
traditional security) of the single-bit secure encryption scheme"].

**Proof sketch.** Fix a non-uniform PPT `D`. At each `n` choose `(m₀ⁿ, m₁ⁿ)` maximizing the
advantage of `D.distinguisherL n` between `pkEncDist n m₀` and `pkEncDist n m₁` of `S.bitwise`
(`Finset.exists_max_image`). By `bitwise_enc_runAtL` and the coin split
`(Fin (n · B n) → Bool) ≃ (Fin n → Fin (B n) → Bool)` (`FunFamily.blocks`, `coinBlock` of
`List.ofFn`; `acceptProb_comp_equiv`), the two samples are the shared-key tuples of
`distAdv_multi_le_sum` with `P := pk`, `E pk [b] r := Enc(1^n, ⟨pk, [b]⟩; r)`, `q := n − 1`
(for `n = 0` the advantage is `0`), after moving the string encoding into `D`
(`distAdv_comp`). Hence the advantage is at most `∑_{j<n}` of the advantages of
`hybridPlant E m₀ m₁ j D` between the single-bit encryptions of `m₀ⁿ_j` and `m₁ⁿ_j`, each at
most that of the machine `B_j`: advice `⟨⟨1^j, ⟨ofFn m₀ⁿ, ofFn m₁ⁿ⟩⟩, D.advice n⟩`
(`NUPPT.exists_withAdvice`), coins `var · S.enc.coins + D.coins` (`NUPPT.exists_split`), which
on `⟨pk, c⟩` encrypts the first `j` bits of `m₁ⁿ` and the last `n − j − 1` bits of `m₀ⁿ` with
`blockEncFun` (one-bit blocks, `blockEncFun_spec`), assembles the tuple
`encodeList l₁ ++ ⟨c, []⟩ ++ encodeList l₂` (`encodeList_eq_flatMap`, `pairEncode_nil_append`),
and runs `D` (`NUPPT.exists_comp`); by `singleBitSecure_iff` applied to `h` (and the `(b, b)` pairs
being `0`) each term is `≤ ε_j(n)`. Over a single machine `B` with the index `j` in the advice
(`Finset.exists_max_image` over `j`), the total is `≤ n · ε(n)`, negligible by
`Negligible.mul_pow`; the maximality of `(m₀ⁿ, m₁ⁿ)` gives the uniform bound. (Formally: `acceptProb_bitwise_pkEncDist`
reads the ciphertexts as `multiDist` with one-bit blocks, and `exists_hybridBound` with
`K := var`, `L := const 1` supplies the single machine `B` and the bound `n · ε(n)`.) -/
theorem SingleBitSecure.bitwise {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    S.bitwise.Secure := by
  intro D
  -- the worst message pair at each parameter (hard-wired into the reduction)
  have hmax : ∀ n, ∃ p : (Fin n → Bool) × (Fin n → Bool), ∀ q : (Fin n → Bool) × (Fin n → Bool),
      distAdv (S.bitwise.pkEncDist n q.1) (S.bitwise.pkEncDist n q.2) (D.distinguisherL n) ≤
        distAdv (S.bitwise.pkEncDist n p.1) (S.bitwise.pkEncDist n p.2) (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun q : (Fin n → Bool) × (Fin n → Bool) =>
        distAdv (S.bitwise.pkEncDist n q.1) (S.bitwise.pkEncDist n q.2) (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun q => hp q (Finset.mem_univ q)⟩
  choose μ hμ using hmax
  -- the hybrid machine for the worst pairs: `n` positions, one-bit blocks
  obtain ⟨B, hB⟩ := exists_hybridBound S.gen S.enc D S.enc_uniform .var (.const 1)
    (fun n i _ => (μ n).1 i) (fun n i _ => (μ n).2 i)
  obtain ⟨ε, hε, hBε⟩ := h B
  refine ⟨fun n => (n : ℝ) * ε n, EnsembleLemmas.negligible_polyExpr_mul .var hε, fun n m₀ m₁ => ?_⟩
  refine (hμ n (m₀, m₁)).trans ?_
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans ((distAdv_def _ _ _).symm.trans_le (hBε n false false))
  have hsingle : ∀ msg msg' : Fin 1 → Bool,
      distAdv (singleDist S.gen S.enc n 1 msg) (singleDist S.gen S.enc n 1 msg')
        (B.distinguisherL n) ≤ ε n := by
    intro msg msg'
    have h1 : msg = fun _ => msg 0 := funext fun i => congrArg msg (Subsingleton.elim i 0)
    have h2 : msg' = fun _ => msg' 0 := funext fun i => congrArg msg' (Subsingleton.elim i 0)
    rw [h1, h2, ← S.pkEncDist_eq_singleDist, ← S.pkEncDist_eq_singleDist]
    exact hBε n _ _
  have hn := hB n (ε n) hε0 hsingle
  rw [distAdv_def] at hn ⊢
  rw [acceptProb_bitwise_pkEncDist, acceptProb_bitwise_pkEncDist]
  exact hn

end BitPublicKeyScheme

/-! ## Single ⇒ multi-message security for public-key encryption [PS10, p. 103] -/

/-- **For public-key encryption, single-message security implies multi-message security**
[PS10, p. 103, "multi-message security is equivalent to single-message security … We leave it as
an exercise to the reader"].

**Proof sketch.** Fix `D` and `q`. At each `n` choose `(mⁿ, m'ⁿ)` maximizing the advantage of
`D.distinguisherL n` between `pkMultiEncDist n (q n) m` and `pkMultiEncDist n (q n) m'`
(`Finset.exists_max_image`). The samples are the shared-key tuples of `distAdv_multi_le_sum`
with `P := pk ∘ Gen`, `E pk m r := Enc(1^n, ⟨pk, m⟩; r)` after moving the tuple encoding into `D`
(`distAdv_comp`), so the advantage is at most `∑_{j ≤ q n}` of the advantages of
`hybridPlant E mⁿ m'ⁿ j D` between `pkEncDist n (mⁿ_j)` and `pkEncDist n (m'ⁿ_j)`. Each is the
advantage of the machine `B_j`: advice `⟨⟨1^j, ⟨ofFn mⁿ, ofFn m'ⁿ⟩⟩, D.advice n⟩`
(`NUPPT.exists_withAdvice`, bound `2(q+1)·var + …`), coins `q · S.enc.coins + D.coins`
(`NUPPT.exists_split`), which on `⟨pk, c⟩` encrypts the other `q n` messages with
`blockEncFun` (`n`-bit blocks, `blockEncFun_spec`), plants `c` at position `j`
(`encodeList_eq_flatMap`, `pairEncode_nil_append`) and runs `D` (`NUPPT.exists_comp`); by `h`
each term is `≤ ε(n)` for the single machine `B` with the index `j` in its advice (take the
maximizing `j` per `n`), so the total is `≤ (q n + 1) ε(n)`, negligible by `Negligible.mul_pow`
and `PolyExpr.eval_le`; maximality of `(mⁿ, m'ⁿ)` gives the uniform bound. (Formally:
`exists_hybridBound` with `K := q + 1`, `L := var` on the samplers `singleDist`/`multiDist`,
which are `pkEncDist`/`pkMultiEncDist` definitionally.) -/
theorem PublicKeyScheme.Secure.multiMessageSecure {S : PublicKeyScheme} (h : S.Secure) :
    S.MultiMessageSecure := by
  intro D q
  -- the worst pair of message vectors at each parameter (hard-wired into the reduction)
  have hmax : ∀ n, ∃ p : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
      ∀ p' : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool),
        distAdv (S.pkMultiEncDist n (q.eval n) p'.1) (S.pkMultiEncDist n (q.eval n) p'.2)
            (D.distinguisherL n) ≤
          distAdv (S.pkMultiEncDist n (q.eval n) p.1) (S.pkMultiEncDist n (q.eval n) p.2)
            (D.distinguisherL n) := by
    intro n
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
      (fun p' : (Fin (q.eval n + 1) → Fin n → Bool) × (Fin (q.eval n + 1) → Fin n → Bool) =>
        distAdv (S.pkMultiEncDist n (q.eval n) p'.1) (S.pkMultiEncDist n (q.eval n) p'.2)
          (D.distinguisherL n))
      Finset.univ_nonempty
    exact ⟨p, fun p' => hp p' (Finset.mem_univ p')⟩
  choose μ hμ using hmax
  -- the hybrid machine for the worst pairs: `q + 1` positions, `n`-bit blocks
  obtain ⟨B, hB⟩ := exists_hybridBound S.gen S.enc D S.enc_uniform (.add q (.const 1)) .var
    (fun n => (μ n).1) (fun n => (μ n).2)
  obtain ⟨ε, hε, hBε⟩ := h B
  refine ⟨fun n => (((PolyExpr.add q (.const 1)).eval n : ℕ) : ℝ) * ε n,
    EnsembleLemmas.negligible_polyExpr_mul _ hε, fun n m m' => ?_⟩
  refine (hμ n (m, m')).trans ?_
  have hε0 : 0 ≤ ε n := (abs_nonneg _).trans (hBε n (fun _ => false) (fun _ => false))
  exact hB n (ε n) hε0 fun msg msg' => hBε n msg msg'

end TCSlib.Cryptography
```


## ===== TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.Defs
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of public-key encryption

[PS10, Definition 171.5], the public-key form of Definition 168.1: `(pk, sk) ← Gen(1^n)`;
`(m₀, m₁, state) ← A^{O₁(sk)}(1^n, pk)`; `c ← Enc_pk(m_b)`; output `A^{O₂(sk)}(c, state)`. The
oracle pairs are `[·, ·]` (CPA), `[Dec, ·]` (CCA1) and `[Dec, Dec*]` (CCA2), where `Dec*` answers
every query except the challenge. There is no encryption oracle: the adversary holds `pk`.
The trapdoor application of Claim 172.a is in `Composability.PublicKey`.

**Its encoding.** As in the private-key game (`Encryption/PrivateKey/OracleSecurity.lean`), one
machine plays both phases. It takes `pk` and queries the bit-string oracles `Dec` and `Challenge`.
The oracle state records the challenge and uses it to gate `Dec` by phase (`decOpen`).

**Fixed lengths by canonical padding** (ruling of 2026-11-05). The codec's oracles take and return
fixed-length strings. Public-key schemes of the ch. 2–4 layer have ciphertexts of varying length,
for example Algorithm 104.3's `⟨f_i(r), b ⊕ m⟩`. A generic wrapper (`FixedLengthPKScheme.ofPadded`)
pads every ciphertext `c` to `L(n)` bits as `⟨c, 1^{L(n) − 2|c| − 2}⟩` (`padCt`). Its decryptor
answers `⊥` on every string that is not such a canonical padding (`isPadded`). Without that check
the padded scheme would be malleable: changing a padding bit of the challenge gives a different
string that decrypts to the same message, which breaks CCA2. Padding is a bijection between
ciphertexts and canonical strings (`pairFstD_padCt`, `padCt_of_isPadded`). So `Dec*` refusing the
padded challenge is `Dec*` refusing the challenge. A bound `L` always exists
(`PublicKeyScheme.exists_padBound`, from the machines' time bounds).

**Deviations** (beyond those of Definition 168.1): ciphertexts reach the adversary padded, and
`Dec` takes only `L(n)`-bit queries, so it decrypts only ciphertexts with `2|c| + 2 ≤ L(n)`.
Security is stated for each admissible `L`; a larger `L` admits longer `Dec` queries.

## Main definitions

* `Composability.padCt`, `Composability.isPadded`: canonical padding and its test.
* `Composability.FixedLengthPKScheme`: a public-key scheme with `msgLen(n)`-bit messages and
  `ctLen(n)`-bit ciphertexts; `FixedLengthPKScheme.ofPadded` builds one by padding.
* `PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`: the ch. 2–4 schemes, padded.
* `FixedLengthPKScheme.indImpl`, `indGame`, `INDSecure`: [PS10, Definition 171.5].

## Main results

* `pairFstD_padCt`, `isPadded_padCt`, `padCt_of_isPadded`: padding is a bijection onto the
  canonical strings.
* `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
* `BitPublicKeyScheme.SingleBitSecure.padded_cpa` (stated; a `sorry` under its sketch): single-bit
  security gives CPA security.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it on Construction 104.3 (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Canonical padding -/

/-- **Canonical padding** of a ciphertext `c` to `L` bits: `⟨c, 1^{L − 2|c| − 2}⟩`. -/
def padCt (L : ℕ) (c : List Bool) : List Bool :=
  pairEncode c (List.replicate (L - (2 * c.length + 2)) true)

/-- Padding pairs `c` with `L - (2 * c.length + 2)` true bits. -/
theorem padCt_eq (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl

/-- Whether `w` is a canonical padding: a pair `⟨c, s⟩` whose second part `s` is all `true`. -/
def isPadded (w : List Bool) : Bool :=
  decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)

/-- The canonical-padding test checks that `w` is its decoded pair and that its second
component contains no false bit. -/
theorem isPadded_eq (w : List Bool) :
    isPadded w =
      (decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)) := rfl

/-- A padding to `L ≥ 2|c| + 2` bits has `L` bits. -/
theorem length_padCt {L : ℕ} {c : List Bool} (h : 2 * c.length + 2 ≤ L) :
    (padCt L c).length = L := by
  simp only [padCt, length_pairEncode, List.length_replicate]
  omega

/-- Unpadding recovers the ciphertext. -/
@[simp] theorem pairFstD_padCt (L : ℕ) (c : List Bool) : pairFstD (padCt L c) = c := by
  simp [padCt]

/-- A padding is canonical. -/
theorem isPadded_padCt (L : ℕ) (c : List Bool) : isPadded (padCt L c) = true := by
  simp [isPadded, padCt, BinArith.hasFalse_eq]

/-- A canonical string is the padding of its first part to its own length. -/
theorem padCt_of_isPadded {w : List Bool} (h : isPadded w = true) :
    padCt w.length (pairFstD w) = w := by
  simp only [isPadded, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h₁, h₂⟩ := h
  have hall : pairSndD w = List.replicate (pairSndD w).length true := by
    refine List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩
    cases b
    · simp only [BinArith.hasFalse_eq, List.any_eq_false, List.mem_map, id_eq,
        forall_exists_index, and_imp] at h₂
      exact absurd rfl (h₂ _ false hb rfl)
    · rfl
  have hlen : w.length = 2 * (pairFstD w).length + 2 + (pairSndD w).length := by
    conv_lhs => rw [← h₁]
    simp only [length_pairEncode]
  unfold padCt
  rw [hlen, show 2 * (pairFstD w).length + 2 + (pairSndD w).length -
    (2 * (pairFstD w).length + 2) = (pairSndD w).length by omega, ← hall]
  exact h₁

/-- The canonical test is polynomial-time. -/
theorem polyTimeComputable_isPadded : PolyTimeComputable (fun w => [isPadded w]) := by
  have heq : PolyTimeComputable fun w => [decide (pairEncode (pairFstD w) (pairSndD w) = w)] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD).pairEncode
        polyTimeComputable_id) using 1
    funext w
    simp [Function.comp_apply]
  exact polyTimeComputable_and heq
    (polyTimeComputable_not (BinArith.polyTimeComputable_hasFalse.comp polyTimeComputable_pairSndD))

/-! ### The padded encryptor and decryptor -/

/-- The padded encryptor's string function: run `Enc` on the same parameter, argument and coins,
and pad its ciphertext to `L(n)` bits. -/
def padEncFun (enc : NUPPT) (L : PolyExpr) (z : List Bool) : List Bool :=
  padCt (L.eval (NUPPT.inParam z).length)
    (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)))

/-- The padded encryptor's string function pads the original output at the same parameter,
argument and coins, with empty advice, to the length prescribed by `L`. -/
theorem padEncFun_eq (enc : NUPPT) (L : PolyExpr) (z : List Bool) :
    padEncFun enc L z = padCt (L.eval (NUPPT.inParam z).length)
      (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z))) := rfl

/-- The padded encryptor is polynomial-time. -/
theorem polyTimeComputable_padEncFun (enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (padEncFun enc L) := by
  have ho : PolyTimeComputable fun z =>
      enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)) :=
    enc.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  have h := ho.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ho.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp NUPPT.polyTimeComputable_inParam)))
  convert h using 1
  funext z
  simp [padEncFun, padCt, Function.comp_apply, length_pairEncode]

/-- The padded decryptor's string function on `⟨sk, w⟩`: `Dec ⟨sk, c⟩` if `w` is the canonical
padding of `c`, and `⊥` otherwise, here `true :: w`, one bit longer than the query. -/
def padDecFun (dec : List Bool → List Bool) (z : List Bool) : List Bool :=
  if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
  else true :: pairSndD z

/-- The padded decryptor decrypts the unpadded query when its canonical test passes and
returns `true :: pairSndD z` otherwise. -/
theorem padDecFun_eq (dec : List Bool → List Bool) (z : List Bool) :
    padDecFun dec z =
      if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
      else true :: pairSndD z := rfl

/-- The padded decryptor is polynomial-time when `Dec` is. -/
theorem polyTimeComputable_padDecFun {dec : List Bool → List Bool}
    (hdec : PolyTimeComputable dec) : PolyTimeComputable (padDecFun dec) :=
  polyTimeComputable_ite (polyTimeComputable_isPadded.comp polyTimeComputable_pairSndD)
    (hdec.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    ((polyTimeComputable_const [true]).append polyTimeComputable_pairSndD)

/-- The padded encryptor as a machine, with the coins of `Enc`. -/
noncomputable abbrev padEnc (enc : NUPPT) (L : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor uses the original encryptor's coin polynomial. -/
theorem padEnc_coins (enc : NUPPT) (L : PolyExpr) : (padEnc enc L).coins = enc.coins :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor pads the ciphertext of the uniform `Enc` with the same coin string,
read in `enc` through the public `padEnc_coins` identification. -/
theorem runAt_padEnc {enc : NUPPT} (henc : enc.Uniform) (L : PolyExpr) (n : ℕ) (y : List Bool)
    (r : (padEnc enc L).Coins n) : (padEnc enc L).runAt n y r =
      padCt (L.eval n) (enc.runAt n y (NUPPT.coinsCongr (padEnc_coins enc L) n r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, henc.runAt_eq,
    NUPPT.coinsCongr_ofFn]
  simp only [padEncFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- The padded decryptor on a padding is `Dec`. -/
theorem padDecFun_padCt (dec : List Bool → List Bool) (sk c : List Bool) (L : ℕ) :
    padDecFun dec (pairEncode sk (padCt L c)) = dec (pairEncode sk c) := by
  simp [padDecFun, isPadded_padCt]

/-- The padded decryptor answers a non-canonical query `w` with a string of `|w| + 1` bits. -/
theorem padDecFun_of_not_isPadded (dec : List Bool → List Bool) (sk w : List Bool)
    (hw : isPadded w = false) : padDecFun dec (pairEncode sk w) = true :: w := by
  simp [padDecFun, hw]

/-! ### Fixed-length public-key schemes -/

/-- A **public-key scheme with fixed-length ciphertexts** [PS10, Definition 102.1]: `msgLen(n)`-bit
messages; `Gen(1^n) = ⟨pk, sk⟩`; `Enc_pk(m)` activated on `⟨pk, m⟩`, whose ciphertexts under
generated keys have `ctLen(n)` bits; a deterministic polynomial-time `Dec` on `⟨sk, c⟩`, with
`⊥` any output that decodes to no message; perfect correctness. -/
structure FixedLengthPKScheme where
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The ciphertext length. -/
  ctLen : PolyExpr
  /-- The key generator. -/
  gen : NUPPT
  /-- The encryptor. -/
  enc : NUPPT
  /-- The decryptor. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
  /-- Ciphertexts under generated keys have `ctLen(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
    (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length =
      ctLen.eval n

namespace FixedLengthPKScheme

/-- **The padded scheme**: a public-key scheme with ciphertexts padded to `L(n)` bits, given that
`L` bounds the honest ciphertexts (`2|c| + 2 ≤ L(n)`) and the message length (so that `⊥` on a
non-canonical `L(n)`-bit query, `|w| + 1` bits, decodes to no message). -/
noncomputable def ofPadded (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (_hmsg : ∀ n, msgLen.eval n ≤ L.eval n) : FixedLengthPKScheme where
  msgLen := msgLen
  ctLen := L
  gen := gen
  enc := padEnc enc L
  dec := padDecFun dec
  gen_uniform := gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_padDecFun dec_poly
  correct := by
    intro n m rg re
    rw [runAt_padEnc enc_uniform, padDecFun_padCt]
    exact correct n m rg (NUPPT.coinsCongr (padEnc_coins enc L) n re)
  enc_length := by
    intro n rg m re
    rw [runAt_padEnc enc_uniform]
    exact length_padCt (hL n rg m (NUPPT.coinsCongr (padEnc_coins enc L) n re))

section PaddedReaders

variable (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, msgLen.eval n ≤ L.eval n)

/-- The padded constructor preserves the supplied message-length polynomial. -/
theorem ofPadded_msgLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).msgLen =
      msgLen := rfl

/-- The padded constructor's ciphertext-length polynomial is `L`. -/
theorem ofPadded_ctLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).ctLen =
      L := rfl

/-- The padded constructor preserves the supplied key generator. -/
theorem ofPadded_gen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).gen =
      gen := rfl

/-- The padded constructor uses `padEnc enc L` as its encryptor. -/
theorem ofPadded_enc :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).enc =
      padEnc enc L := rfl

/-- The padded constructor uses `padDecFun dec` as its decryptor. -/
theorem ofPadded_dec :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).dec =
      padDecFun dec := rfl

end PaddedReaders

end FixedLengthPKScheme

/-- **A ch. 2–4 public-key scheme, padded** to `L(n)`-bit ciphertexts. -/
noncomputable def _root_.TCSlib.Cryptography.PublicKeyScheme.padded (S : PublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded .var S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n m rg re => S.correct n m rg re) L hL hmsg

section PublicKeyPaddedReaders

variable (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n)

/-- Padding a public-key scheme preserves its message-length polynomial `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.var := rfl

/-- The padded public-key scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded public-key scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded public-key scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end PublicKeyPaddedReaders

/-- **A ch. 2–4 single-bit public-key scheme, padded** to `L(n)`-bit ciphertexts: one-bit
messages, `Enc` activated on `⟨pk, [b]⟩`. -/
noncomputable def _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded (S : BitPublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded (.const 1) S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n (m : Fin 1 → Bool) rg re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm, S.correct n (m 0) rg re, ← hm, decodeFin_ofFn])
    L
    (fun n rg (m : Fin 1 → Bool) re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm]
      exact hL n rg (m 0) re)
    hmsg

section BitPublicKeyPaddedReaders

variable (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n)

/-- Padding a single-bit public-key scheme preserves its constant one-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.const 1 := rfl

/-- The padded single-bit scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a single-bit public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded single-bit scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded single-bit scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end BitPublicKeyPaddedReaders

/-- **A padding bound exists** for every ch. 2–4 public-key scheme, from the time bounds of
`Gen` and `Enc` (`NUPPT.length_runAt_le_runLenPoly`): `|pk| ≤ Q₁(n)`, the input `⟨pk, m⟩` has at
most `2Q₁(n) + 2 + n` bits, and the ciphertext at most `Q₂(n)`; `L = 2Q₂ + 2 + n` works.

**Proof sketch.** Bound the generator's output by its running-time polynomial, which also
bounds its public-key projection. The pair-encoding length formula then bounds the encryptor's
input by `2Q₁(n) + 2 + n`. Applying the encryptor's output-length bound to this input gives
`Q₂(n)`. Choose `L(n) = 2Q₂(n) + 2 + n`: it covers the ciphertext's pair-encoding overhead and
is at least the message length `n`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.exists_padBound (S : PublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
          + 2 ≤ L.eval n) ∧ ∀ n, n ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)).length ≤
        (PolyExpr.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var).eval
          n := by
    intro n rg m
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  refine ⟨.add (.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var))) (.const 2))
      .var, fun n rg m re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg m) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

/-- **A padding bound exists** for every ch. 2–4 single-bit public-key scheme (as for
`PublicKeyScheme.exists_padBound`).

**Proof sketch.** The generator's output-length bound also bounds the public key by `Q₁(n)`.
Pairing that key with one bit gives an encryptor input of at most `2Q₁(n) + 3` bits. Its
running-time bound therefore supplies a ciphertext-length polynomial `Q₂(n)`. The polynomial
`L(n) = 2Q₂(n) + 2` covers the ciphertext encoding and is at least one, as required for the
single-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.exists_padBound (S : BitPublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
          ≤ L.eval n) ∧ ∀ n, 1 ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (b : Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]).length ≤
        (PolyExpr.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)).eval n := by
    intro n rg b
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_singleton, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  refine ⟨.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)))) (.const 2),
      fun n rg b re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg b) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-! ### The experiment of Definition 171.5 -/

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The query lengths of the two oracles `Dec` and `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => S.msgLen.eval n + S.msgLen.eval n

/-- Decryption queries have the scheme's ciphertext length. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = S.ctLen.eval n := rfl

/-- Challenge queries contain two messages of the scheme's message length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` a ciphertext. -/
def outLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n

/-- Decryption answers contain a validity bit followed by one message. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.msgLen.eval n + 1 := rfl

/-- Challenge answers have the scheme's ciphertext length. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl

/-- The two oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 2) := bitSpec (S.inLens n) (S.outLens n)

/-- The public-key IND oracle specification is the bit specification at the scheme's query
and answer lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Oracle `i` accepts bit strings of length `S.inLens n i`. -/
theorem indSpec_dom (n : ℕ) (i : Fin 2) :
    (S.indSpec n).dom i = (Fin (S.inLens n i) → Bool) :=
  bitSpec_dom (S.inLens n) (S.outLens n) i

/-- Oracle `i` returns bit strings of length `S.outLens n i`. -/
theorem indSpec_rng (n : ℕ) (i : Fin 2) :
    (S.indSpec n).rng i = (Fin (S.outLens n i) → Bool) :=
  bitSpec_rng (S.inLens n) (S.outLens n) i

/-- **The oracles of `Ind_b`** at parameter `n`, for the keys `pk`, `sk`; the state is the
challenge, once asked.
- `Dec` answers `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not the challenge, and
  `⊥` (all `false`) otherwise; an output that decodes to no message is `⊥` as well.
- `Challenge` answers `Enc_pk(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c)

/-- A decryption query checks oracle availability and refuses the recorded challenge;
otherwise it returns the decoded plaintext with its validity flag, preserving the state. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits _, s) := rfl

/-- The first challenge query encrypts the selected message half using fresh coins and
records the padded ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c) := rfl

/-- A repeated challenge query returns the recorded ciphertext and preserves it as state. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (c, some c) := rfl

/-- Under CPA, `Dec` never answers. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n pk sk 0 c s = .pure (zeroBits _, s) := by
  simp [indImpl, FixedLengthScheme.decOpen_cpa]

/-- Under CCA2, `Dec` refuses the challenge. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n pk sk 0 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, FixedLengthScheme.decOpen_cca2]

/-- The codec of the adversary: the two oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The public-key IND codec decodes a move with the bit decoder at the scheme's oracle
lengths and a one-bit final output. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The public-key IND codec encodes an entry by pairing the unary oracle index with its
query and answer strings. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The public-key IND codec returns the false one-bit result on timeout. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- **The experiment `Ind_b(Π, A, n)`** [PS10, Definition 171.5] for the attack `atk`, with query
budget `q`: sample `(pk, sk) ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the oracles
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res => .pure (res.1 0)

/-- The public-key IND game samples key-generation and adversary coins, simulates the
oracles on the public-key input from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)))
        (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security of a public-key scheme** [PS10, Definition 171.5]: for every
non-uniform PPT `A` and every polynomial query budget, `A`'s advantage between `Ind_0` and
`Ind_1` is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- Public-key IND security is exactly negligible advantage for every non-uniform PPT
adversary and polynomial query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthPKScheme

/-! ### From ensemble security to CPA -/

/-- **Single-bit security gives CPA security** for a padded single-bit scheme.

**Proof sketch.**
1. With CPA there is no `Dec` oracle, so the adversary's view is `pk`, its coins and the padded
   challenge `padCt L (Enc_pk(m_b))`, where its messages `m₀, m₁ ∈ {0,1}` are chosen after
   seeing `pk`.
2. If `m₀ = m₁` both games are identical. Otherwise `m_b` is `b` or `¬b`. The distinguisher `D`
   on `⟨pk, c⟩` runs `A` on `pk` (its first move gives `m₀, m₁`), answers the challenge with
   `padCt L c`, and outputs `A`'s bit, flipped when `(m₀, m₁) = (1, 0)` and replaced by `0` when
   `m₀ = m₁`.
3. Conditioning on `A`'s choice, `A`'s CPA advantage is at most `D`'s single-bit advantage
   between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`, which is negligible
   (`BitPublicKeyScheme.singleBitSecure_iff`). T1 (`Games.exists_handlerMachine`) makes
   `D` a machine: `advIn` extracts `pk` from `z = ⟨pk, c⟩`, the handler answers the challenge
   with `padCt L c`, and `out` flips or zeroes the result bit as described above. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : (S.padded L hL hmsg).INDSecure .cpa := by
  sorry

end TCSlib.Cryptography.Composability
```


## ===== TCSlib/Cryptography/LWE/Assumption.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Encoding
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-sample decisional LWE against non-uniform PPT machines

## Main definitions

* `TCSlib.Cryptography.LWE.Family`: numeric parameters and scalar noise indexed by a
  separate security parameter, with polynomial dimension, sample and residue-width bounds.
* `Family.inputBitsBound`: a syntactic polynomial bounding the encoded challenge length.
* `Family.advantageAt`: the concrete LWE advantage of a machine on the fixed encoding.
* `DLWEAssumption`: every non-uniform PPT machine has negligible decision advantage.

## Main results

* `Family.inputBitsBound_eq`, `Family.advantageAt_eq`, `dlweAssumption_iff` expose the
  budget and security predicate through their public interfaces.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1, Definition 26.8 (non-uniform PPT adversaries).

**Scope.** A family fixes one sample schedule. `DLWEAssumption` does not silently quantify
over every polynomial sample schedule. All rows of the experiment use one uniform common
secret, and each error coordinate uses an independent seed for the scalar `Noise` law.
This law is a finite rational distribution, not a claim of exact Gaussian sampling.

The modulus may grow with the parameter, but its chosen binary width is a `PolyExpr` and
the residue-width bound prevents truncation. Polynomial dimension and sample bounds give
a polynomial challenge length, so an adversary's running time in its input length is also
polynomial in the security parameter on these challenges.

`Family` and `DLWEAssumption` assert no efficient parameter generator, residue sampler or
noise sampler. Executable constructions must provide those contracts separately. A first
exact fair-bit implementation can use power-of-two moduli and explicit finite bit-seed
noise; non-dyadic laws require a separate implemented sampler or approximation transfer.
No search-LWE or worst-case lattice reduction is asserted.
-/

namespace TCSlib.Cryptography.LWE

open Complexity

/-- A fixed-sample asymptotic decisional LWE family [Pei16, Definition 4.2.3], using
the repository's non-uniform PPT convention [PS10, Definition 26.8]. The security
parameter is independent of dimension, sample count, modulus and scalar noise.

**Convention.** The syntactic polynomials are upper bounds, not an assertion that the
numeric parameter schedule or noise sampler is uniformly computable. Honest-sampler
efficiency and any statistical approximation are separate construction obligations. -/
structure Family where
  /-- Numeric dimension, sample count and modulus at each security parameter. -/
  parameters : ℕ → Parameters
  /-- The actual scalar finite-seed noise law at each security parameter. -/
  noise : ℕ → Noise
  /-- A syntactic polynomial upper bound on the secret dimension. -/
  dimensionBound : PolyExpr
  /-- A syntactic polynomial upper bound on the fixed sample schedule. -/
  samplesBound : PolyExpr
  /-- The fixed-width binary representation of each residue. -/
  residueBits : PolyExpr
  /-- The dimension is polynomially bounded in the independent security parameter. -/
  dimension_le : ∀ κ, (parameters κ).dimension ≤ dimensionBound.eval κ
  /-- The chosen number of samples is polynomially bounded. -/
  samples_le : ∀ κ, (parameters κ).samples ≤ samplesBound.eval κ
  /-- Every residue fits in the selected width; no modular entry is truncated. -/
  modulus_le_pow : ∀ κ, (parameters κ).modulus ≤ 2 ^ (residueBits.eval κ)

namespace Family

/-- The syntactic polynomial `samplesBound * (dimensionBound + 1) * residueBits`
majorizes the challenge's matrix-plus-vector bit length. This is representation
accounting for the fixed-sample experiment of [Pei16, Definition 4.2.3]. -/
def inputBitsBound (F : Family) : PolyExpr :=
  .mul (.mul F.samplesBound (.add F.dimensionBound (.const 1))) F.residueBits

/-- `F.inputBitsBound` is the expression
`samplesBound * (dimensionBound + 1) * residueBits`. -/
theorem inputBitsBound_eq (F : Family) :
    F.inputBitsBound =
      .mul (.mul F.samplesBound (.add F.dimensionBound (.const 1))) F.residueBits := rfl

/-- Every challenge supplied to a distinguisher fits the family's polynomial input budget.

**Proof sketch.** Substitute `encodeChallenge_length`, bound the dimension and sample
count by the family's fields, and read the multiplication/addition equations of `PolyExpr`.
All factors are natural numbers, so multiplication preserves the inequalities. -/
theorem encodeChallenge_length_le (F : Family) (κ : ℕ)
    (x : Matrix (Fin (F.parameters κ).samples) (Fin (F.parameters κ).dimension)
      (ZMod (F.parameters κ).modulus) ×
      (Fin (F.parameters κ).samples → ZMod (F.parameters κ).modulus)) :
    (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x).length ≤
      F.inputBitsBound.eval κ := by
  rw [encodeChallenge_length, inputBitsBound_eq, PolyExpr.eval_mul, PolyExpr.eval_mul,
    PolyExpr.eval_add, PolyExpr.eval_const]
  exact Nat.mul_le_mul_right _
    (Nat.mul_le_mul (F.samples_le κ) (Nat.add_le_add_right (F.dimension_le κ) 1))

/-- The decision advantage of a non-uniform PPT machine at security parameter `κ`
on the canonical encoding of `(A,A s+e)` versus uniform `(A,u)`
[Pei16, Definition 4.2.3; PS10, Definition 26.8]. Machine coins are independent of the
matrix, common secret and coordinate-noise seeds. -/
noncomputable def advantageAt (F : Family) (D : NUPPT) (κ : ℕ) : ℝ :=
  decisionAdvantage (F.parameters κ) (F.noise κ)
    (fun x r => D.distinguisherL κ
      (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x) r)

/-- `F.advantageAt D κ` is `decisionAdvantage` with `D.distinguisherL κ` applied to
the fixed-width challenge encoding. -/
theorem advantageAt_eq (F : Family) (D : NUPPT) (κ : ℕ) :
    F.advantageAt D κ = decisionAdvantage (F.parameters κ) (F.noise κ)
      (fun x r => D.distinguisherL κ
        (encodeChallenge (F.parameters κ) (F.residueBits.eval κ) x) r) := rfl

end Family

/-- The fixed-sample decisional LWE assumption: every non-uniform PPT machine has
negligible absolute decision advantage [Pei16, Definition 4.2.3; PS10, Definition 26.8].
The sample schedule is the one stored in `F.parameters`; a statement for all polynomial
sample schedules requires an additional outer quantifier. This is a proposition supplied
as a hypothesis by consumers, not a theorem or a new axiom. -/
def DLWEAssumption (F : Family) : Prop :=
  ∀ D : NUPPT, Negligible fun κ => F.advantageAt D κ

/-- `DLWEAssumption F` holds exactly when `F.advantageAt D` is negligible for every
non-uniform PPT machine `D`. -/
theorem dlweAssumption_iff (F : Family) :
    DLWEAssumption F ↔ ∀ D : NUPPT, Negligible fun κ => F.advantageAt D κ := Iff.rfl

end TCSlib.Cryptography.LWE
```


## ===== TCSlib/Cryptography/LWE/Basic.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Noise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Numeric parameters and the finite-sample LWE map

## Main definitions

* `TCSlib.Cryptography.LWE.Parameters`: dimension, sample count and modulus at least two.
* `noisyValues`: the value vector `A s + e` modulo the modulus.
* `sample`: publish a uniform matrix with noisy values for one common uniform secret.

## Main results

* `noisyValues_apply`, `sample_fst`, `sample_snd` are the owner-side readings of the maps.
* `binaryErrorSum_bound` bounds a binary subset sum of magnitude-bounded errors.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.2.1 and 4.2.3 and Section 5.2.1.

**Convention.** Rows are samples, so `A` is `m` by `n` and secrets multiply on the right.
This is the transpose of the row-secret convention in [Pei16]. A uniform seed for `sample`
is a product: the matrix, one secret, and one independent scalar-noise seed per row.
The type permits zero samples for boundary checks; it asserts no hardness or nonvacuity.
-/

namespace TCSlib.Cryptography.LWE

/-- Numeric parameters for `m` LWE samples in dimension `n` modulo `q >= 2`
[Pei16, Definitions 4.2.1 and 4.2.3]. Noise is an explicit separate argument and the
asymptotic security parameter is not identified with any of these three numbers. -/
structure Parameters where
  /-- The dimension of the common secret. -/
  dimension : ℕ
  /-- The number of rows sampled under that same secret. -/
  samples : ℕ
  /-- The modulus of the sample equations. -/
  modulus : ℕ
  /-- The modulus is at least two, excluding the zero and trivial residue rings. -/
  modulus_ge_two : 2 ≤ modulus

instance (P : Parameters) : NeZero P.modulus :=
  ⟨Nat.ne_of_gt (lt_of_lt_of_le (Nat.zero_lt_succ 1) P.modulus_ge_two)⟩

/-- The LWE value vector is the matrix-secret product plus coordinatewise integer
errors reduced modulo `P.modulus` [Pei16, Definition 4.2.1, transposed convention]. -/
def noisyValues (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ) :
    Fin P.samples → ZMod P.modulus :=
  A.mulVec s + fun i => (e i : ZMod P.modulus)

/-- Coordinate `i` of the noisy value vector is the inner product of row `i` with
the common secret, plus integer error `e i` reduced modulo the modulus. -/
theorem noisyValues_apply (P : Parameters)
    (A : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus))
    (s : Fin P.dimension → ZMod P.modulus) (e : Fin P.samples → ℤ) (i : Fin P.samples) :
    noisyValues P A s e i = (∑ j, A i j * s j) + (e i : ZMod P.modulus) := rfl

/-- A subset selected by a binary mask has absolute sum at most `m*B` when
each of the `m` integer errors has magnitude at most `B`
[Pei16, Section 5.2.1, deterministic bounded-support specialization].

**Proof sketch.** Apply the triangle inequality to the sum. Every selected error
has magnitude at most `B`, and every unselected term is zero. Sum the uniform
bound over all coordinates. -/
theorem binaryErrorSum_bound {m : ℕ} (e : Fin m → ℤ) (r : Fin m → Bool)
    (B : ℕ) (he : ∀ i, (e i).natAbs ≤ B) :
    (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤ m * B := by
  calc
    (∑ i, e i * ((r i).toNat : ℤ)).natAbs ≤
        ∑ i : Fin m, (e i * ((r i).toNat : ℤ)).natAbs :=
      Finset.le_sum_of_subadditive Int.natAbs (by decide)
        (fun x y => Int.natAbs_add_le x y) Finset.univ _
    _ ≤ ∑ _i : Fin m, B := by
      apply Finset.sum_le_sum
      intro i _
      cases r i
      · simp only [Bool.toNat_false, Nat.cast_zero, mul_zero, Int.natAbs_zero]
        exact Nat.zero_le B
      · simpa only [Bool.toNat_true, Nat.cast_one, mul_one] using he i
    _ = m * B := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_id]

/-- The LWE sampler publishes `(A, A s + e)` with one common secret for all rows
[Pei16, Definition 4.2.3]. A uniform input chooses the matrix and secret independently
and supplies independent scalar-noise seeds to the rows. -/
def sample (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  (r.1, noisyValues P r.1 r.2.1 (fun i => χ.sample (r.2.2 i)))

/-- The public matrix of `sample P χ r` is the matrix component of its seed. -/
theorem sample_fst (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (sample P χ r).1 = r.1 := rfl

/-- The public values of `sample P χ r` use the single secret `r.2.1` and the scalar
noise sampled independently by the coordinate seeds `r.2.2`. -/
theorem sample_snd (P : Parameters) (χ : Noise)
    (r : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) × (Fin P.samples → χ.Coins))) :
    (sample P χ r).2 = noisyValues P r.1 r.2.1 (fun i => χ.sample (r.2.2 i)) := rfl

end TCSlib.Cryptography.LWE
```


## ===== TCSlib/Cryptography/LWE/Noise.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite-seed integer noise for LWE

## Main definitions

* `TCSlib.Cryptography.LWE.Noise`: a scalar integer sampler on a finite nonempty seed type.
* `Noise.Bounded`: every seed produces an error of absolute value at most a given bound.

## Main results

* `Noise.bounded_iff` reads the support bound without unfolding its predicate.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.1.

**Deviation.** This implementation-facing noise model is the pushforward of a uniform
finite seed. It describes finite rational laws, with seed multiplicities retained, and
does not describe an exact infinite discrete Gaussian. No efficient sampler is asserted.
Independent seeds per coordinate specify independent copies of the scalar law.
-/

namespace TCSlib.Cryptography.LWE

/-- A scalar integer error is sampled by applying `sample` to a uniform element of the
finite nonempty type `Coins` [Pei16, Definition 4.2.1, finite-seed specialization].
Repeated images of seeds retain their multiplicities; the law need not be uniform on
the support. This structure asserts neither efficient samplability nor LWE hardness. -/
structure Noise where
  /-- The finite type of seeds, sampled uniformly. -/
  Coins : Type
  /-- The seed type is finite. -/
  [fintype : Fintype Coins]
  /-- The seed type is nonempty, so uniform seeds form a probability distribution. -/
  [nonempty : Nonempty Coins]
  /-- The integer error produced by a seed, before reduction modulo the LWE modulus. -/
  sample : Coins → ℤ

attribute [instance] Noise.fintype Noise.nonempty

namespace Noise

/-- Every seed produces an integer error of absolute value at most `B` [Pei16,
Definition 4.2.1, bounded-noise specialization used for perfect correctness]. -/
def Bounded (χ : Noise) (B : ℕ) : Prop := ∀ r : χ.Coins, (χ.sample r).natAbs ≤ B

/-- The scalar noise is bounded by `B` exactly when every seed's integer error has
natural absolute value at most `B`. -/
theorem bounded_iff (χ : Noise) (B : ℕ) :
    χ.Bounded B ↔ ∀ r : χ.Coins, (χ.sample r).natAbs ≤ B := Iff.rfl

end Noise

end TCSlib.Cryptography.LWE
```


## ===== TCSlib/Cryptography/LWE/BitNoise.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Noise
import TCSlib.Cryptography.Foundations.Probability
import Mathlib.Data.Fin.Tuple.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Explicit bit-seed noise laws

## Main definitions

* `bitNoise`: the existing finite-noise bundle with an explicit fixed-length bit seed.
* `centeredValue`, `centeredNoise`: difference of two independent bit counts.

## Main results

The law equation retains seed multiplicities. The centered profile has support in
`[-t,t]`, a symmetric law and mean zero. These exact-law claims are proved below.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.1 (the scalar error law).

The bit samplers and centered profile are disclosed finite-law repository
specializations, not exact discrete Gaussians. No hardness assumption, Gaussian
approximation, parameter computability or polynomial-time machine is inferred.
-/

namespace TCSlib.Cryptography.LWE

/-- Bundle a specified `t`-bit integer sampler as the actual finite LWE noise law
[Pei16, Definition 4.2.1, explicit finite-bit specialization]. -/
def bitNoise (t : ℕ) (f : (Fin t → Bool) → ℤ) : Noise where
  Coins := Fin t → Bool
  sample := f

/-- The seed type of `bitNoise t f` is the full type of `t`-bit words. -/
theorem bitNoise_Coins (t : ℕ) (f : (Fin t → Bool) → ℤ) :
    (bitNoise t f).Coins = (Fin t → Bool) := rfl

/-- Sampling `bitNoise t f` applies the specified function to all seed bits. -/
theorem bitNoise_sample (t : ℕ) (f : (Fin t → Bool) → ℤ) (r : Fin t → Bool) :
    (bitNoise t f).sample r = f r := rfl

/-- An output's probability is its number of bit-seed preimages divided by `2^t`.
Repeated outputs retain their multiplicities [Pei16, Definition 4.2.1, finite-law
specialization].

**Proof sketch.** Apply `uprob_eq_card_filter` to the complete bit-seed type and
evaluate its cardinality as `2^t`. This asserts the actual law, not uniform support. -/
theorem bitNoise_probability (t : ℕ) (f : (Fin t → Bool) → ℤ) (z : ℤ) :
    uprob (fun r : (bitNoise t f).Coins => (bitNoise t f).sample r = z) =
      ((Finset.univ.filter fun r : Fin t → Bool => f r = z).card : ℝ) / (2 ^ t : ℕ) := by
  classical
  simpa only [bitNoise_sample, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    using (uprob_eq_card_filter (fun r : Fin t → Bool => f r = z))

/-- Subtract the count of true bits in the second block from the count in the first.
This centered finite profile is a repository specialization of the noise-law slot
in [Pei16, Definition 4.2.1]. -/
def centeredValue (t : ℕ) (r : Fin (t + t) → Bool) : ℤ :=
  (∑ i : Fin t, ((r (Fin.castAdd t i)).toNat : ℤ)) -
    ∑ i : Fin t, ((r (Fin.natAdd t i)).toNat : ℤ)

/-- The centered output is exactly the difference of the two integer bit counts. -/
theorem centeredValue_eq (t : ℕ) (r : Fin (t + t) → Bool) :
    centeredValue t r = (∑ i : Fin t, ((r (Fin.castAdd t i)).toNat : ℤ)) -
      ∑ i : Fin t, ((r (Fin.natAdd t i)).toNat : ℤ) := rfl

/-- The centered-noise bundle uses exactly `t+t` independent fair seed bits. -/
def centeredNoise (t : ℕ) : Noise := bitNoise (t + t) (centeredValue t)

/-- The centered-noise bundle is the explicit two-block bit-noise instance. -/
theorem centeredNoise_eq (t : ℕ) :
    centeredNoise t = bitNoise (t + t) (centeredValue t) := rfl

/-- The centered sampler uses exactly the full pair of `t`-bit seed blocks. -/
theorem centeredNoise_Coins (t : ℕ) :
    (centeredNoise t).Coins = (Fin (t + t) → Bool) := rfl

/-- The centered sampler's sample projection is exactly its integer two-count difference. -/
theorem centeredNoise_sample (t : ℕ) (r : Fin (t + t) → Bool) :
    (centeredNoise t).sample r = centeredValue t r := rfl

/-- Every centered-noise output has absolute value at most `t`.

**Proof sketch.** Each bit count lies between zero and `t`. Their integer difference
lies in `[-t,t]`, including the empty two-block seed at `t=0`. -/
theorem centeredNoise_bounded (t : ℕ) : (centeredNoise t).Bounded t := by
  rw [Noise.bounded_iff]
  intro r
  rw [centeredNoise_sample, centeredValue_eq]
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
  have hnonneg (g : Fin t → Bool) :
      0 ≤ ∑ i : Fin t, ((g i).toNat : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  have hle (g : Fin t → Bool) :
      (∑ i : Fin t, ((g i).toNat : ℤ)) ≤ (t : ℤ) := by
    calc
      (∑ i : Fin t, ((g i).toNat : ℤ)) ≤ ∑ _i : Fin t, (1 : ℤ) :=
        Finset.sum_le_sum (fun i _ => Int.ofNat_le.mpr (Bool.toNat_le (g i)))
      _ = (t : ℤ) := by simp
  exact abs_sub_le_of_nonneg_of_le
    (hnonneg (fun i => r (Fin.castAdd t i)))
    (hle (fun i => r (Fin.castAdd t i)))
    (hnonneg (fun i => r (Fin.natAdd t i)))
    (hle (fun i => r (Fin.natAdd t i)))

/-- Negating an output preserves its probability under the centered profile.

**Proof sketch.** Complement every seed bit by an involution. Each block count
becomes `t` minus its old count, so their difference is negated. Relabeling the
uniform seed preserves each event probability. -/
theorem centeredValue_symmetric (t : ℕ) (z : ℤ) :
    uprob (fun r : Fin (t + t) → Bool => centeredValue t r = z) =
      uprob (fun r : Fin (t + t) → Bool => centeredValue t r = -z) := by
  let e : (Fin (t + t) → Bool) ≃ (Fin (t + t) → Bool) :=
    Function.Involutive.toPerm (fun r : Fin (t + t) → Bool => fun i => !(r i))
      (by intro r; funext i; exact Bool.not_not (r i))
  have he (r : Fin (t + t) → Bool) (i : Fin (t + t)) : e r i = !(r i) := rfl
  have hbit (b : Bool) : ((!b).toNat : ℤ) = 1 - (b.toNat : ℤ) := by
    cases b <;> decide
  have hn (r : Fin (t + t) → Bool) :
      centeredValue t (e r) = -centeredValue t r := by
    rw [centeredValue_eq, centeredValue_eq]
    simp_rw [he, hbit]
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, sub_sub_sub_cancel_left, neg_sub]
  simpa only [hn, neg_inj] using
    (uprob_comp_equiv e (fun r : Fin (t + t) → Bool => centeredValue t r = -z))

/-- The centered profile has exactly zero real expectation.

**Proof sketch.** Distribute both integer bit counts and interchange the finite
sums. A coordinate permutation identifies the uniform sums for any two positions,
so the corresponding contributions from the two blocks cancel. -/
theorem centeredValue_mean (t : ℕ) :
    uexp (fun r : Fin (t + t) → Bool => (centeredValue t r : ℝ)) = 0 := by
  classical
  have hcoord (a b : Fin (t + t)) :
      (∑ r : Fin (t + t) → Bool, ((r a).toNat : ℝ)) =
        ∑ r : Fin (t + t) → Bool, ((r b).toNat : ℝ) := by
    let e := Equiv.arrowCongr (Equiv.swap a b) (Equiv.refl Bool)
    have h := e.sum_comp (fun r : Fin (t + t) → Bool => ((r b).toNat : ℝ))
    simpa only [e, Equiv.arrowCongr_apply, Equiv.refl_apply,
      Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right] using h
  have hz : (∑ r : Fin (t + t) → Bool, (centeredValue t r : ℝ)) = 0 := by
    simp only [centeredValue_eq, Int.cast_sub, Int.cast_sum,
      Int.cast_natCast, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    calc
      (∑ r : Fin (t + t) → Bool, ∑ i : Fin t,
          ((r (Fin.castAdd t i)).toNat : ℝ)) =
        ∑ i : Fin t, ∑ r : Fin (t + t) → Bool,
          ((r (Fin.castAdd t i)).toNat : ℝ) := Finset.sum_comm
      _ = ∑ i : Fin t, ∑ r : Fin (t + t) → Bool,
          ((r (Fin.natAdd t i)).toNat : ℝ) :=
        Finset.sum_congr rfl (fun i _ => hcoord (Fin.castAdd t i) (Fin.natAdd t i))
      _ = ∑ r : Fin (t + t) → Bool, ∑ i : Fin t,
          ((r (Fin.natAdd t i)).toNat : ℝ) := Finset.sum_comm
  rw [uexp_def, hz, zero_div]

end TCSlib.Cryptography.LWE
```


## ===== TCSlib/Cryptography/LWE/Sampling.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.BitNoise
import TCSlib.Cryptography.LWE.Experiments
import TCSlib.Cryptography.Encoding.DyadicUniform

import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Actual LWE laws from independent bit blocks

## Main definitions

* `sampleFromBits`: sample a matrix, one common secret, and independent bit-noise seeds.
* `uniformFromBits`: sample an independent full matrix and value vector.

## Main results

The pushforward and acceptance statements identify exactly the existing LWE and
uniform experiments under a dyadic-modulus hypothesis. The noise law remains the
specified `bitNoise`, without a Gaussian or uniform-support substitution.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definitions 4.2.1 and 4.2.3.

This is an explicit fair-bit specialization of the existing finite-noise model.
These statements describe finite maps and laws. Uniform parameter computation,
noise-machine efficiency, and the all-polynomial common-secret sample schedule
are additional obligations, not consequences of exact sampling at one parameter.
-/

namespace TCSlib.Cryptography.LWE

open Encoding.DyadicUniform
open TCSlib.InformationTheory

/-- Apply the existing LWE sample map to disjoint matrix blocks, one secret vector's
blocks, and independent scalar-noise seeds [Pei16, Definition 4.2.3, dyadic adaptation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def sampleFromBits (P : Parameters) (width t : ℕ) (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  sample P (bitNoise t f)
    (bitsToMatrix width r.1, bitsToVector width r.2.1, r.2.2)

/-- The bit implementation uses the original sample map and the same row-noise seeds. -/
theorem sampleFromBits_eq (P : Parameters) (width t : ℕ) (f : (Fin t → Bool) → ℤ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
    sampleFromBits P width t f r = sample P (bitNoise t f)
      (bitsToMatrix width r.1, bitsToVector width r.2.1, r.2.2) := rfl

/-- Uniform independent bit blocks induce exactly the real LWE distribution.

**Proof sketch.** Product the matrix and secret bit-reader bijections, retaining
the noise seed vector by the identity equivalence. Relabel uniform seeds and apply
the public pushforward equation to the original common-secret sampler. -/
theorem sampleFromBits_law (P : Parameters) (width t : ℕ)
    (hq : P.modulus = 2 ^ width) (f : (Fin t → Bool) → ℤ) :
    (FinDist.uniform ((Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool)))).map
      (sampleFromBits P width t f) =
    (FinDist.uniform (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      ((Fin P.dimension → ZMod P.modulus) ×
        (Fin P.samples → (bitNoise t f).Coins)))).map (sample P (bitNoise t f)) := by
  classical
  let eA := Equiv.ofBijective
    (bitsToMatrix (q := P.modulus) (rows := P.samples) (columns := P.dimension) width)
    (bitsToMatrix_bijective width hq)
  let eS := Equiv.ofBijective
    (bitsToVector (q := P.modulus) (length := P.dimension) width)
    (bitsToVector_bijective width hq)
  let e := eA.prodCongr
    (eS.prodCongr (Equiv.refl (Fin P.samples → Fin t → Bool)))
  have he (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      ((Fin P.dimension → Fin width → Bool) × (Fin P.samples → Fin t → Bool))) :
      sampleFromBits P width t f r = sample P (bitNoise t f) (e r) := by
    rw [sampleFromBits_eq]
    rfl
  have hc := Fintype.card_congr e
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.map_apply, Finset.sum_filter, Finset.sum_filter]
  simp only [FinDist.uniform_apply, bitNoise_Coins]
  rw [hc]
  exact Fintype.sum_equiv e _ _ (fun r => by rw [he r])

/-- The exact real-law implementation preserves every independently randomized test.

**Proof sketch.** Apply the existing acceptance-as-averaged-pushforward equation
on both sides and substitute `sampleFromBits_law`. The averaging equation retains
the independent distinguisher coins. -/
theorem acceptProb_sampleFromBits {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters) (width t : ℕ) (hq : P.modulus = 2 ^ width)
    (f : (Fin t → Bool) → ℤ)
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) :
    acceptProb (sampleFromBits P width t f) D = acceptProb (sample P (bitNoise t f)) D := by
  classical
  rw [acceptProb_eq_uexp_sum_map, acceptProb_eq_uexp_sum_map,
    sampleFromBits_law P width t hq f]

/-- Read independent matrix and value-vector blocks for the comparison distribution
[Pei16, Definition 4.2.3, dyadic adaptation]. -/
@[simps! (config := { isSimp := false }) fst snd]
def uniformFromBits (P : Parameters) (width : ℕ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      (Fin P.samples → Fin width → Bool)) :
    Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus) :=
  (bitsToMatrix width r.1, bitsToVector width r.2)

/-- The comparison sampler reads the matrix and value vector from disjoint blocks. -/
theorem uniformFromBits_eq (P : Parameters) (width : ℕ)
    (r : (Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      (Fin P.samples → Fin width → Bool)) :
    uniformFromBits P width r = (bitsToMatrix width r.1, bitsToVector width r.2) := rfl

/-- The comparison bit sampler induces exactly the independent uniform challenge law.

**Proof sketch.** Take the product of the matrix and value-vector reader bijections.
Its uniform pushforward is the uniform distribution on their product. -/
theorem uniformFromBits_law (P : Parameters) (width : ℕ)
    (hq : P.modulus = 2 ^ width) :
    (FinDist.uniform ((Fin P.samples → Fin P.dimension → Fin width → Bool) ×
      (Fin P.samples → Fin width → Bool))).map (uniformFromBits P width) =
      FinDist.uniform (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
        (Fin P.samples → ZMod P.modulus)) := by
  classical
  let eA := Equiv.ofBijective
    (bitsToMatrix (q := P.modulus) (rows := P.samples) (columns := P.dimension) width)
    (bitsToMatrix_bijective width hq)
  let eV := Equiv.ofBijective
    (bitsToVector (q := P.modulus) (length := P.samples) width)
    (bitsToVector_bijective width hq)
  let e := eA.prodCongr eV
  have he : uniformFromBits P width = fun r => e r := by
    funext r
    rw [uniformFromBits_eq]
    rfl
  rw [he]
  apply FinDist.ext
  intro y
  have hf : (Finset.univ.filter fun r => e r = y) = {e.symm y} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hr
      exact e.injective (hr.trans (e.apply_symm_apply y).symm)
    · rintro rfl
      exact e.apply_symm_apply y
  simp only [FinDist.map_apply, hf, Finset.sum_singleton,
    FinDist.uniform_apply, Fintype.card_congr e]

end TCSlib.Cryptography.LWE
```


## ===== TCSlib/Cryptography/LWE/BitEncoding.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.LWE.Basic
import Mathlib.Data.ZMod.ValMinAbs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit codepoints and bounded-error decoding for Regev encryption

## Main definitions

* `BitEncoding.codepoint`: zero for false and `floor(q/2)` for true.
* `BitEncoding.distance`: circular distance using Mathlib's minimal integer lift.
* `BitEncoding.decode`: choose the nearer codepoint, breaking ties toward false.

## Main results

The distance lemmas and `decode_codepoint_add` are proved below.
The last theorem gives perfect decoding under the strict separation condition
`2 * B < q / 2`, with natural-number division.

## References

* [Wu24] D. Wu, CS395T *Topics in Cryptography*, Spring 2024 lecture notes,
  compilation last updated 30 April 2024, Definition 20.5 and Lecture 21.

**Deviation.** Nearest-codepoint decoding replaces the notes' informal rounding
notation. The strict separation condition covers arbitrary moduli, both error signs
and all finite parameters. The decoder is total, with an explicit tie rule. No exact
Gaussian sampling, tail bound or machine implementation is asserted.
-/

namespace TCSlib.Cryptography.LWE.BitEncoding

/-- The codepoint for a bit is zero or `floor(q/2)` modulo `q`
[Wu24, Definition 20.5]. -/
def codepoint (P : Parameters) (b : Bool) : ZMod P.modulus :=
  if b then ((P.modulus / 2 : ℕ) : ZMod P.modulus) else 0

/-- `codepoint P b` is `q/2` cast to residues when `b` is true and zero otherwise. -/
theorem codepoint_eq (P : Parameters) (b : Bool) :
    codepoint P b = if b then ((P.modulus / 2 : ℕ) : ZMod P.modulus) else 0 := rfl

/-- Circular distance is the natural absolute value of Mathlib's minimal integer
representative of `x - y`. This is technical decoding infrastructure. -/
def distance (P : Parameters) (x y : ZMod P.modulus) : ℕ :=
  (x - y).valMinAbs.natAbs

/-- The circular distance is `(x - y).valMinAbs.natAbs`. -/
theorem distance_eq (P : Parameters) (x y : ZMod P.modulus) :
    distance P x y = (x - y).valMinAbs.natAbs := rfl

/-- Circular distance is symmetric.

**Proof sketch.** Rewrite `y - x` as the negative of `x - y` and use the public
`ZMod.natAbs_valMinAbs_neg` lemma. -/
theorem distance_symm (P : Parameters) (x y : ZMod P.modulus) :
    distance P x y = distance P y x := by
  rw [distance_eq, distance_eq, ← neg_sub x y, ZMod.natAbs_valMinAbs_neg]

/-- Circular distance satisfies the triangle inequality.

**Proof sketch.** Write `x - z = (x - y) + (y - z)`. Apply
`ZMod.natAbs_valMinAbs_add_le`, then the integer absolute-value triangle inequality. -/
theorem distance_triangle (P : Parameters) (x y z : ZMod P.modulus) :
    distance P x z ≤ distance P x y + distance P y z := by
  rw [distance_eq, distance_eq, distance_eq, ← sub_add_sub_cancel x y z]
  exact (ZMod.natAbs_valMinAbs_add_le (x - y) (y - z)).trans
    (Int.natAbs_add_le _ _)

/-- Adding the same residue to both arguments preserves circular distance.

**Proof sketch.** Cancel the common translation in the difference and read `distance_eq`. -/
theorem distance_add_right (P : Parameters) (x y a : ZMod P.modulus) :
    distance P (x + a) (y + a) = distance P x y := by
  rw [distance_eq, distance_eq, add_sub_add_right_eq_sub]

/-- The two bit codepoints have circular distance `floor(q/2)`
[Wu24, Definition 20.5, exact separation].

**Proof sketch.** Use `ZMod.valMinAbs_natCast_of_le_half` for `q/2` and
`ZMod.natAbs_valMinAbs_neg` if the subtraction has the opposite sign. -/
theorem distance_codepoints (P : Parameters) :
    distance P (codepoint P false) (codepoint P true) = P.modulus / 2 := by
  rw [codepoint_eq, codepoint_eq]
  simp only [Bool.false_eq_true, if_false, if_true]
  rw [distance_eq, zero_sub, ZMod.natAbs_valMinAbs_neg,
    ZMod.valMinAbs_natCast_of_le_half (le_refl _), Int.natAbs_natCast]

/-- Reducing an integer error modulo the modulus cannot increase its distance
from zero beyond its original natural absolute value.

**Proof sketch.** Use `ZMod.coe_valMinAbs`, `ZMod.natAbs_valMinAbs_le` and
`ZMod.natAbs_min_of_le_div_two` to compare the minimal lift with the given integer. -/
theorem distance_intCast_zero_le (P : Parameters) (e : ℤ) :
    distance P (e : ZMod P.modulus) 0 ≤ e.natAbs := by
  rw [distance_eq, sub_zero]
  exact ZMod.natAbs_min_of_le_div_two P.modulus _ e
    (ZMod.coe_valMinAbs _) (ZMod.natAbs_valMinAbs_le _)

/-- Decode to true precisely when the true codepoint is strictly nearer;
equidistant inputs decode to false [Wu24, Definition 20.5, specified tie convention]. -/
def decode (P : Parameters) (x : ZMod P.modulus) : Bool :=
  decide (distance P x (codepoint P true) < distance P x (codepoint P false))

/-- Decoding compares the two circular distances, with a strict inequality for true. -/
theorem decode_eq (P : Parameters) (x : ZMod P.modulus) :
    decode P x =
      decide (distance P x (codepoint P true) < distance P x (codepoint P false)) := rfl

/-- An error of absolute value at most `B` preserves the encoded bit whenever
`2 * B < floor(q/2)` [Wu24, Definition 20.5 and Lecture 21, bounded-error refinement].

**Proof sketch.** Translation invariance and the integer-error bound put the received
residue within `B` of its intended codepoint. The triangle inequality and exact
codepoint separation put its distance to the other codepoint above `B`. The intended
codepoint is uniquely nearer, so the tie rule is immaterial for valid encryptions. -/
theorem decode_codepoint_add (P : Parameters) (B : ℕ) (b : Bool) (e : ℤ)
    (he : e.natAbs ≤ B) (hsep : 2 * B < P.modulus / 2) :
    decode P (codepoint P b + (e : ZMod P.modulus)) = b := by
  have herr : distance P (codepoint P b + (e : ZMod P.modulus)) (codepoint P b) ≤ B := by
    calc
      _ = distance P (e : ZMod P.modulus) 0 := by
        simpa only [zero_add, add_comm] using
          distance_add_right P (e : ZMod P.modulus) 0 (codepoint P b)
      _ ≤ e.natAbs := distance_intCast_zero_le P e
      _ ≤ B := he
  have htri := distance_triangle P (codepoint P false)
    (codepoint P b + (e : ZMod P.modulus)) (codepoint P true)
  rw [distance_codepoints, distance_symm P (codepoint P false)] at htri
  cases b
  · rw [decode_eq]
    exact decide_eq_false (by omega)
  · rw [decode_eq]
    exact decide_eq_true (by omega)

end TCSlib.Cryptography.LWE.BitEncoding
```


## ===== TCSlib/Cryptography/LWE/Encoding.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.LWE.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary encoding of decisional LWE challenges

## Main definitions

* `TCSlib.Cryptography.LWE.encodeChallenge`: the row-major public matrix followed by
  the value vector, with one fixed-width binary numeral per residue.

## Main results

* `encodeChallenge_eq` exposes the concatenation through the common modular encoders.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.2.3.

**Representation convention.** The dimensions and width are fixed by the family at the
security parameter; no delimiters are needed within a challenge. The width must satisfy
`P.modulus <= 2^width` for the encoding to retain all residues. The LWE asymptotic family
carries this bound. The challenge has `P.samples * (P.dimension + 1) * width` bits.
Faithfulness and length are proved below; this module asserts no
efficiency of sampling the mathematical LWE distribution.
-/

namespace TCSlib.Cryptography.LWE

/-- Encode the LWE challenge `(A,b)` of [Pei16, Definition 4.2.3] as the row-major
matrix followed by the value vector. Every entry uses the same fixed width, which is
lossless when `P.modulus <= 2^width`. -/
def encodeChallenge (P : Parameters) (width : ℕ)
    (x : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) : List Bool :=
  Encoding.Modular.encodeMatrix width x.1 ++ Encoding.Modular.encodeVector width x.2

/-- `encodeChallenge P width (A,b)` is `encodeMatrix width A` followed by
`encodeVector width b`. -/
theorem encodeChallenge_eq (P : Parameters) (width : ℕ)
    (x : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    encodeChallenge P width x =
      Encoding.Modular.encodeMatrix width x.1 ++ Encoding.Modular.encodeVector width x.2 := rfl

/-- An encoded LWE challenge contains exactly
`P.samples * (P.dimension + 1) * width` bits [Pei16, Definition 4.2.3, bit accounting].

**Proof sketch.** Add the common encoder's matrix length and value-vector length,
then distribute multiplication. -/
theorem encodeChallenge_length (P : Parameters) (width : ℕ)
    (x : Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) :
    (encodeChallenge P width x).length = P.samples * (P.dimension + 1) * width := by
  rw [encodeChallenge_eq, List.length_append, Encoding.Modular.encodeMatrix_length,
    Encoding.Modular.encodeVector_length]
  simp only [Nat.mul_add, Nat.mul_one, Nat.add_mul]

/-- Encoding an LWE challenge is injective if the modulus fits in the residue width.

**Proof sketch.** Split equal strings after the known matrix length. Apply the common
matrix and vector injectivity statements to the two respective segments. -/
theorem encodeChallenge_injective (P : Parameters) (width : ℕ)
    (hwidth : P.modulus ≤ 2 ^ width) :
    Function.Injective (encodeChallenge P width) := by
  intro x y h
  simp only [encodeChallenge_eq] at h
  have hparts := List.append_inj h (by simp only [Encoding.Modular.encodeMatrix_length])
  exact Prod.ext
    (Encoding.Modular.encodeMatrix_injective width hwidth hparts.1)
    (Encoding.Modular.encodeVector_injective width hwidth hparts.2)

end TCSlib.Cryptography.LWE
```


## ===== TCSlib/Cryptography/Encoding/Modular.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import Mathlib.Data.Matrix.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed-width encodings of modular vectors and matrices

## Main definitions

* `TCSlib.Cryptography.Encoding.Modular.encodeVector`: concatenate the fixed-width
  binary numerals of a residue vector in increasing coordinate order.
* `encodeMatrix`: concatenate the encoded rows of a matrix in increasing row order.

## Main results

* `encodeVector_eq`, `encodeMatrix_eq` expose the two concatenations.
* The length and injectivity theorems establish their representation guarantees.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definitions 4.1.1 and 4.2.3 (the modular inputs being represented).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (binary-string machine inputs).

**Representation convention.** These encodings are repository plumbing, rather than
additional lattice assumptions. Each residue uses its representative in `[0,q)`, written
most significant bit first by the existing public `Candidates.natToList`. A width `k`
represents every residue without truncation when `q <= 2^k`. The definitions are total at
smaller widths, where the numeral operation keeps only low-order bits; consumers must
supply the width bound before using faithfulness. The LWE and SIS asymptotic families
carry that bound. No polynomial-time machine implementation is asserted here.

The vector length is `length * width` and the matrix length is `rows * columns * width`.
The length and injectivity theorems below prove this accounting and losslessness under
the width bound. They assert no efficient machine implementation or hardness property.
-/

namespace TCSlib.Cryptography.Encoding.Modular

/-- Encode a modular vector in increasing coordinate order, using the public fixed-width
numeral operation. For `q <= 2^width` no residue is truncated. This is the binary
representation convention for the vectors in [Pei16, Definitions 4.1.1 and 4.2.3]. -/
def encodeVector {q length : ℕ} [NeZero q] (width : ℕ)
    (v : Fin length → ZMod q) : List Bool :=
  (List.ofFn fun i => Candidates.natToList width (v i).val).flatten

/-- `encodeVector width v` concatenates `natToList width (v i).val` over coordinates
`i` in increasing order. -/
theorem encodeVector_eq {q length : ℕ} [NeZero q] (width : ℕ)
    (v : Fin length → ZMod q) :
    encodeVector width v =
      (List.ofFn fun i => Candidates.natToList width (v i).val).flatten := rfl

/-- Encode a modular matrix row by row, with columns increasing within each row.
For `q <= 2^width` no entry is truncated. This fixes the binary representation of the
matrices in [Pei16, Definitions 4.1.1 and 4.2.3]. -/
def encodeMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (A : Matrix (Fin rows) (Fin columns) (ZMod q)) : List Bool :=
  (List.ofFn fun i => encodeVector width (A i)).flatten

/-- `encodeMatrix width A` concatenates `encodeVector width (A i)` over rows `i`
in increasing order. -/
theorem encodeMatrix_eq {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (A : Matrix (Fin rows) (Fin columns) (ZMod q)) :
    encodeMatrix width A = (List.ofFn fun i => encodeVector width (A i)).flatten := rfl

/-- A vector encoding has exactly `length * width` bits.

**Proof sketch.** Every numeral has length `width` by the existing numeral-length
lemma. Sum these equal lengths over the `length` coordinate blocks. -/
theorem encodeVector_length {q length : ℕ} [NeZero q] (width : ℕ)
    (v : Fin length → ZMod q) :
    (encodeVector width v).length = length * width := by
  rw [encodeVector_eq, List.length_flatten, ← List.ofFn_comp']
  simp only [Candidates.length_natToList, List.ofFn_const, List.sum_replicate_nat]

/-- A matrix encoding has exactly `rows * columns * width` bits.

**Proof sketch.** Each encoded row has `columns * width` bits by
`encodeVector_length`; concatenate `rows` such blocks and reassociate multiplication. -/
theorem encodeMatrix_length {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (A : Matrix (Fin rows) (Fin columns) (ZMod q)) :
    (encodeMatrix width A).length = rows * columns * width := by
  rw [encodeMatrix_eq, List.length_flatten, ← List.ofFn_comp']
  simp only [encodeVector_length, List.ofFn_const, List.sum_replicate_nat, Nat.mul_assoc]

/-- Fixed-width vector encoding is injective when every residue fits in that width.

**Proof sketch.** Cut equal encoded strings into their fixed-width coordinate blocks.
The existing numeral round-trip lemma recovers each representative, since it is less
than `q` and `q <= 2^width`. Equal representatives give equal residues at every coordinate.
The zero-coordinate and modulus-one/zero-width cases are included. -/
theorem encodeVector_injective {q length : ℕ} [NeZero q] (width : ℕ)
    (hwidth : q ≤ 2 ^ width) :
    Function.Injective (encodeVector (q := q) (length := length) width) := by
  intro v w h
  have hblocks :
      List.ofFn (fun i => Candidates.natToList width (v i).val) =
        List.ofFn (fun i => Candidates.natToList width (w i).val) := by
    apply List.eq_iff_flatten_eq.mpr
    refine ⟨?_, ?_⟩
    · simpa only [encodeVector_eq] using h
    · rw [← List.ofFn_comp', ← List.ofFn_comp']
      simp only [Candidates.length_natToList]
  have hcoordinate := List.ofFn_injective hblocks
  funext i
  apply ZMod.val_injective q
  exact Candidates.natToList_injOn
    (lt_of_lt_of_le (ZMod.val_lt (v i)) hwidth)
    (lt_of_lt_of_le (ZMod.val_lt (w i)) hwidth)
    (congrFun hcoordinate i)

/-- Fixed-width row-major matrix encoding is injective when every residue fits.

**Proof sketch.** Cut equal encodings into equal fixed-length row blocks using
`encodeVector_length`, then apply `encodeVector_injective` to every row. Empty row or
column sets represent the unique matrix on an empty index product. -/
theorem encodeMatrix_injective {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hwidth : q ≤ 2 ^ width) :
    Function.Injective (encodeMatrix (q := q) (rows := rows) (columns := columns) width) := by
  intro A B h
  have hrows :
      List.ofFn (fun i => encodeVector width (A i)) =
        List.ofFn (fun i => encodeVector width (B i)) := by
    apply List.eq_iff_flatten_eq.mpr
    refine ⟨?_, ?_⟩
    · simpa only [encodeMatrix_eq] using h
    · rw [← List.ofFn_comp', ← List.ofFn_comp']
      simp only [encodeVector_length]
  have hcoordinate := List.ofFn_injective hrows
  funext i
  exact encodeVector_injective width hwidth (congrFun hcoordinate i)

end TCSlib.Cryptography.Encoding.Modular
```


## ===== TCSlib/Cryptography/Encoding/DyadicUniform.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.ModularDecode
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Exact uniform sampling of dyadic modular data

## Main definitions

* `bitsToResidue`: read a fixed number of independent MSB-first bits as a residue.
* `bitsToVector`, `bitsToMatrix`: apply that reader to disjoint coordinate blocks.

## Main results

The bijection and pushforward statements identify the actual uniform sampling laws.
Canonical encoding recovers every input bit when the modulus is exactly a power of two.
The bijections, exact laws and encoding round trips are proved below.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definition 4.2.3 (uniform matrix and secret in the LWE experiment).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (binary random tapes).

This is a repository representation adaptation. Exact fair-bit sampling is asserted
only under `q = 2^width`; no rejection sampler or approximation for odd moduli is
implicit. Width zero, modulus one and empty dimensions are included. These finite
maps do not by themselves establish an efficient uniform parameter schedule.
-/

namespace TCSlib.Cryptography.Encoding.DyadicUniform

open TCSlib.InformationTheory
open TCSlib.Cryptography.NumberTheory (listToNat)

/-- Read the MSB-first word of `width` bits, then cast its value modulo `q`
[Pei16, Definition 4.2.3; PS10, Section 2.1, representation adaptation]. -/
def bitsToResidue {q : ℕ} [NeZero q] (width : ℕ)
    (r : Fin width → Bool) : ZMod q :=
  (listToNat (List.ofFn r) : ZMod q)

/-- The residue reader casts the natural value of the complete input word. -/
theorem bitsToResidue_eq {q : ℕ} [NeZero q] (width : ℕ)
    (r : Fin width → Bool) :
    bitsToResidue (q := q) width r = (listToNat (List.ofFn r) : ZMod q) := rfl

/-- At a power-of-two modulus, the fixed-width residue reader is a bijection.

**Proof sketch.** The numeral reader is less than `2^width`, so taking its
representative loses nothing. The existing fixed-width numeral round trips give
both inverses. At width zero both the seed and residue types have one element. -/
theorem bitsToResidue_bijective {q : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) : Function.Bijective (bitsToResidue (q := q) width) := by
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro r s hrs
    apply List.ofFn_injective
    have recover (v : Fin width → Bool) :
        Candidates.natToList width (bitsToResidue (q := q) width v).val =
          List.ofFn v := by
      rw [bitsToResidue_eq]
      apply Candidates.natToList_val_natCast
        (show (List.ofFn v).length = width from List.length_ofFn)
      simpa only [List.length_ofFn, hq] using
        Candidates.listToNat_lt_two_pow (List.ofFn v)
    exact (recover r).symm.trans
      ((congrArg (fun x : ZMod q => Candidates.natToList width x.val) hrs).trans
        (recover s))
  · simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ZMod.card, hq]

/-- A uniform block of bits induces the full uniform residue law at a dyadic modulus.

**Proof sketch.** Apply the preceding bijection to each singleton fibre of the
uniform pushforward, using `FinDist.map_apply` and `FinDist.uniform_apply`. -/
theorem bitsToResidue_uniform {q : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    (FinDist.uniform (Fin width → Bool)).map (bitsToResidue (q := q) width) =
      FinDist.uniform (ZMod q) := by
  classical
  have hb := bitsToResidue_bijective (q := q) width hq
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.uniform_apply, Finset.sum_filter]
  simp only [FinDist.uniform_apply, Fintype.card_of_bijective hb]
  calc
    (∑ x : Fin width → Bool,
        if bitsToResidue (q := q) width x = y then (Fintype.card (ZMod q) : ℝ)⁻¹ else 0) =
        ∑ z : ZMod q, if z = y then (Fintype.card (ZMod q) : ℝ)⁻¹ else 0 :=
      Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Re-encoding a residue sampled from one full-width block returns all original bits.

**Proof sketch.** The input word has length `width` and value below the modulus.
Read the residue representative and apply the public numeral reconstruction theorem. -/
theorem encode_bitsToResidue {q : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) (r : Fin width → Bool) :
    Candidates.natToList width (bitsToResidue (q := q) width r).val = List.ofFn r := by
  rw [bitsToResidue_eq]
  apply Candidates.natToList_val_natCast
    (show (List.ofFn r).length = width from List.length_ofFn)
  simpa only [List.length_ofFn, hq] using
    Candidates.listToNat_lt_two_pow (List.ofFn r)

/-- Read independent full-width residue blocks as a modular vector
[Pei16, Definition 4.2.3, fair-bit specialization]. -/
def bitsToVector {q length : ℕ} [NeZero q] (width : ℕ)
    (r : Fin length → Fin width → Bool) : Fin length → ZMod q :=
  fun i => bitsToResidue width (r i)

/-- Coordinate `i` is obtained by reading exactly block `r i`. -/
theorem bitsToVector_apply {q length : ℕ} [NeZero q] (width : ℕ)
    (r : Fin length → Fin width → Bool) (i : Fin length) :
    bitsToVector (q := q) width r i = bitsToResidue width (r i) := rfl

/-- Disjoint dyadic residue blocks give a bijection onto the full vector space.

**Proof sketch.** Apply scalar injectivity and surjectivity coordinatewise;
finite function extensionality and choice assemble the inverses. -/
theorem bitsToVector_bijective {q length : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    Function.Bijective (bitsToVector (q := q) (length := length) width) := by
  constructor
  · intro r s h
    funext i
    apply (bitsToResidue_bijective (q := q) width hq).1
    simpa only [bitsToVector_apply] using congrFun h i
  · intro v
    classical
    choose r hr using fun i : Fin length =>
      (bitsToResidue_bijective (q := q) width hq).2 (v i)
    refine ⟨r, ?_⟩
    funext i
    exact (bitsToVector_apply width r i).trans (hr i)

/-- Uniform independent bit blocks give the exact full uniform vector law.

**Proof sketch.** Count singleton fibres using `bitsToVector_bijective` and the
public pushforward equation. Independence is retained by the function-space seed. -/
theorem bitsToVector_uniform {q length : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    (FinDist.uniform (Fin length → Fin width → Bool)).map
      (bitsToVector (q := q) width) = FinDist.uniform (Fin length → ZMod q) := by
  classical
  have hb := bitsToVector_bijective (q := q) (length := length) width hq
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.uniform_apply, Finset.sum_filter]
  simp only [FinDist.uniform_apply, Fintype.card_of_bijective hb]
  calc
    (∑ x : Fin length → Fin width → Bool,
        if bitsToVector (q := q) width x = y then
          (Fintype.card (Fin length → ZMod q) : ℝ)⁻¹ else 0) =
        ∑ z : Fin length → ZMod q,
          if z = y then (Fintype.card (Fin length → ZMod q) : ℝ)⁻¹ else 0 :=
      Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Encoding a sampled vector concatenates the original bit blocks in coordinate order.

**Proof sketch.** Read `Modular.encodeVector_eq`, substitute the scalar reconstruction
theorem in each block, and retain the original increasing-coordinate order. -/
theorem encode_bitsToVector {q length : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) (r : Fin length → Fin width → Bool) :
    Modular.encodeVector width (bitsToVector (q := q) width r) =
      (List.ofFn fun i => List.ofFn (r i)).flatten := by
  simp only [Modular.encodeVector_eq, bitsToVector_apply, encode_bitsToResidue width hq]

/-- Read disjoint row-major bit blocks as a modular matrix
[Pei16, Definition 4.2.3, fair-bit specialization]. -/
def bitsToMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (r : Fin rows → Fin columns → Fin width → Bool) :
    Matrix (Fin rows) (Fin columns) (ZMod q) :=
  fun i => bitsToVector width (r i)

/-- Entry `(i,j)` is obtained by reading block `r i j`. -/
theorem bitsToMatrix_apply {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (r : Fin rows → Fin columns → Fin width → Bool)
    (i : Fin rows) (j : Fin columns) :
    bitsToMatrix (q := q) width r i j = bitsToResidue width (r i j) := rfl

/-- The row-major matrix reader is a bijection at an exact dyadic modulus.

**Proof sketch.** Apply vector bijectivity independently to each row. Empty rows
or columns give a singleton matrix space and require no positive-dimension premise. -/
theorem bitsToMatrix_bijective {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    Function.Bijective (bitsToMatrix (q := q) (rows := rows) (columns := columns) width) := by
  constructor
  · intro r s h
    funext i
    apply (bitsToVector_bijective (q := q) (length := columns) width hq).1
    funext j
    simpa only [bitsToVector_apply, bitsToMatrix_apply] using congrFun (congrFun h i) j
  · intro A
    classical
    choose r hr using fun i : Fin rows =>
      (bitsToVector_bijective (q := q) (length := columns) width hq).2 (A i)
    refine ⟨r, ?_⟩
    funext i j
    exact (bitsToMatrix_apply width r i j).trans
      ((bitsToVector_apply width (r i) j).symm.trans (congrFun (hr i) j))

/-- Uniform matrix blocks induce exactly the full uniform modular matrix distribution.

**Proof sketch.** Count fibres of the matrix bijection using the existing finite
uniform pushforward equations. No entry or column is fixed to a special value. -/
theorem bitsToMatrix_uniform {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) :
    (FinDist.uniform (Fin rows → Fin columns → Fin width → Bool)).map
      (bitsToMatrix (q := q) width) =
        FinDist.uniform (Matrix (Fin rows) (Fin columns) (ZMod q)) := by
  classical
  have hb := bitsToMatrix_bijective (q := q) (rows := rows) (columns := columns) width hq
  apply FinDist.ext
  intro y
  rw [FinDist.map_apply, FinDist.uniform_apply, Finset.sum_filter]
  simp only [FinDist.uniform_apply, Fintype.card_of_bijective hb]
  calc
    (∑ x : Fin rows → Fin columns → Fin width → Bool,
        if bitsToMatrix (q := q) width x = y then
          (Fintype.card (Matrix (Fin rows) (Fin columns) (ZMod q)) : ℝ)⁻¹ else 0) =
        ∑ z : Matrix (Fin rows) (Fin columns) (ZMod q),
          if z = y then
            (Fintype.card (Matrix (Fin rows) (Fin columns) (ZMod q)) : ℝ)⁻¹ else 0 :=
      Fintype.sum_bijective _ hb _ _ (fun _ => rfl)
    _ = _ := by simp

/-- Canonical matrix encoding recovers every row-major input bit block.

**Proof sketch.** Read `Modular.encodeMatrix_eq` and apply vector reconstruction
to each row. The result uses the same row-major ordering as the LWE encoding. -/
theorem encode_bitsToMatrix {q rows columns : ℕ} [NeZero q] (width : ℕ)
    (hq : q = 2 ^ width) (r : Fin rows → Fin columns → Fin width → Bool) :
    Modular.encodeMatrix width (bitsToMatrix (q := q) width r) =
      (List.ofFn fun i => (List.ofFn fun j => List.ofFn (r i j)).flatten).flatten := by
  simp only [Modular.encodeMatrix_eq, Modular.encodeVector_eq, bitsToMatrix_apply,
    encode_bitsToResidue width hq]

end TCSlib.Cryptography.Encoding.DyadicUniform
```


## ===== TCSlib/Cryptography/Encoding/DyadicArithmetic.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Scalar arithmetic for dyadic cryptographic encodings

## Main definitions

* `addPoly`: add two MSB operands and write the result at a polynomial width.
* `mulPoly`: multiply two MSB operands and write the result at that width.
* `subPoly`: subtract modulo the corresponding power of two without natural underflow.

## Main results

Canonical writer equations, exact output widths, ring readings and all three
polynomial-time contracts are proved. They handle arbitrary templates, overlong
operands and zero width. Matrix algorithms, actual-law samplers and cryptographic
primitive-security endpoints remain separate consumer obligations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, Section 2.1 (bit-string machine representations).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009, Section 7.2 (the surrounding machine model).

**Representation adaptation.** These are repository scalar adapters, not exact
textbook arithmetic statements. They consume the proved endian/width interfaces in
`Encoding.BinaryArith` and the public canonical-pair equations and machines in
`Complexity.BinArith.AddSub` and `Mul`. No new arithmetic, traversal or padding host
is introduced. Each polynomial is fixed before selecting a machine.

The input layout is `pairEncode u (pairEncode a b)`. Only the length of the arbitrary
template `u` determines the output width. Total default projections cover malformed
pairs; zero widths and overlong operands are allowed. Subtraction first reduces the
right operand to that width, then adds the modulus to the left operand before using
natural subtraction. The modulus word has only one more bit than the output width.
The ring statements also cover width zero, when the modulus is one; cryptographic
parameter consumers supply any stronger modulus premise separately.
-/

namespace TCSlib.Cryptography.Encoding.DyadicArithmetic

open Complexity Turing
open TCSlib.Cryptography.NumberTheory (listToNat)
open TCSlib.Cryptography.Encoding.BinaryArith

/-- Add the two inner MSB operands and write their sum at the polynomial width
determined by the outer template length [PS10, Section 2.1, repository adaptation].
High bits are discarded, implementing addition modulo the corresponding power of two. -/
def addPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  fromLEPoly p
    (pairEncode (pairFstD z)
      (BinArith.add
        (pairEncode
          (toLE (pairFstD (pairSndD z)))
          (toLE (pairSndD (pairSndD z))))))

/-- `addPoly` converts both inner operands, applies the existing binary adder,
and writes its output with the original outer template. -/
theorem addPoly_eq (p : PolyExpr) (z : List Bool) :
    addPoly p z =
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.add
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z)))))) := rfl

/-- On a nested encoded pair, addition writes the sum of the operand values at
width `p.eval u.length`, allowing arbitrary operand lengths and leading zeros.

**Proof sketch.** Read `addPoly_eq` and the total pair equations. Apply
`toLE_eq_natBits` to both operands and `BinArith.add_pairEncode` to the resulting
canonical pair. Read the outer writer with `fromLEPoly_pairEncode` and
`LogProg.bitsVal_bits`. -/
theorem addPoly_pairEncode (p : PolyExpr) (u a b : List Bool) :
    addPoly p (pairEncode u (pairEncode a b)) =
      Candidates.natToList (p.eval u.length) (listToNat a + listToNat b) := by
  simp only [addPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    toLE_eq_natBits, BinArith.add_pairEncode,
    fromLEPoly_pairEncode, LogProg.bitsVal_bits]

/-- Addition produces exactly the requested width on every raw input, including
malformed outer or inner pairs.

**Proof sketch.** Read `addPoly_eq`, apply `fromLEPoly_length`, and read the first
projection of the reconstructed pair. -/
theorem addPoly_length (p : PolyExpr) (z : List Bool) :
    (addPoly p z).length = p.eval (pairFstD z).length := by
  rw [addPoly_eq, fromLEPoly_length, pairFstD_pairEncode]

/-- The addition output represents the sum of the input values in the residue ring
modulo `2^(p.eval u.length)`, without a fit premise on either operand.

**Proof sketch.** Apply the canonical writer equation and
`Candidates.listToNat_natToList_eq_mod`; remove the remainder under the cast using
`ZMod.natCast_mod` and read the cast of a sum. -/
theorem addPoly_natCast_pairEncode (p : PolyExpr) (u a b : List Bool) :
    (listToNat (addPoly p (pairEncode u (pairEncode a b))) :
        ZMod (2 ^ (p.eval u.length))) =
      (listToNat a : ZMod (2 ^ (p.eval u.length))) +
        (listToNat b : ZMod (2 ^ (p.eval u.length))) := by
  rw [addPoly_pairEncode, Candidates.listToNat_natToList_eq_mod,
    ZMod.natCast_mod, Nat.cast_add]

/-- Scalar addition at any fixed syntactic polynomial width is polynomial-time.

**Proof sketch.** Compose the total projections, `polyTimeComputable_toLE`, pairing,
`BinArith.polyTimeComputable_add`, and `polyTimeComputable_fromLEPoly`. Read
`addPoly_eq` to identify the resulting function. No new machine or host is needed. -/
theorem polyTimeComputable_addPoly (p : PolyExpr) : PolyTimeComputable (addPoly p) := by
  have ha : PolyTimeComputable
      (fun z => toLE (pairFstD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hb : PolyTimeComputable
      (fun z => toLE (pairSndD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h : PolyTimeComputable (fun z =>
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.add
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z))))))) :=
    (polyTimeComputable_fromLEPoly p).comp
      (polyTimeComputable_pairFstD.pairEncode
        (BinArith.polyTimeComputable_add.comp (ha.pairEncode hb)))
  exact (funext (addPoly_eq p)).symm ▸ h

/-- Multiply the two inner MSB operands and write their product at the polynomial
width determined by the outer template [PS10, Section 2.1, repository adaptation].
The output retains the low bits, implementing multiplication modulo a power of two. -/
def mulPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  fromLEPoly p
    (pairEncode (pairFstD z)
      (BinArith.mul
        (pairEncode
          (toLE (pairFstD (pairSndD z)))
          (toLE (pairSndD (pairSndD z))))))

/-- `mulPoly` converts both inner operands, applies the existing binary multiplier,
and writes its output with the original outer template. -/
theorem mulPoly_eq (p : PolyExpr) (z : List Bool) :
    mulPoly p z =
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.mul
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z)))))) := rfl

/-- On a nested encoded pair, multiplication writes the product of the operand values
at width `p.eval u.length`, allowing arbitrary operand lengths.

**Proof sketch.** Read `mulPoly_eq` and the total pair equations, convert with
`toLE_eq_natBits`, apply `BinArith.mul_pairEncode`, and read the outer writer using
`fromLEPoly_pairEncode` and `LogProg.bitsVal_bits`. -/
theorem mulPoly_pairEncode (p : PolyExpr) (u a b : List Bool) :
    mulPoly p (pairEncode u (pairEncode a b)) =
      Candidates.natToList (p.eval u.length) (listToNat a * listToNat b) := by
  simp only [mulPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    toLE_eq_natBits, BinArith.mul_pairEncode,
    fromLEPoly_pairEncode, LogProg.bitsVal_bits]

/-- Multiplication produces exactly the requested width on every raw input.

**Proof sketch.** Read `mulPoly_eq`, apply `fromLEPoly_length`, and read the first
projection of the reconstructed pair. -/
theorem mulPoly_length (p : PolyExpr) (z : List Bool) :
    (mulPoly p z).length = p.eval (pairFstD z).length := by
  rw [mulPoly_eq, fromLEPoly_length, pairFstD_pairEncode]

/-- The multiplication output represents the product in the residue ring modulo
`2^(p.eval u.length)`, without an operand-fit premise.

**Proof sketch.** Read the canonical writer, apply
`Candidates.listToNat_natToList_eq_mod`, then use `ZMod.natCast_mod` and the cast
equation for multiplication. -/
theorem mulPoly_natCast_pairEncode (p : PolyExpr) (u a b : List Bool) :
    (listToNat (mulPoly p (pairEncode u (pairEncode a b))) :
        ZMod (2 ^ (p.eval u.length))) =
      (listToNat a : ZMod (2 ^ (p.eval u.length))) *
        (listToNat b : ZMod (2 ^ (p.eval u.length))) := by
  rw [mulPoly_pairEncode, Candidates.listToNat_natToList_eq_mod,
    ZMod.natCast_mod, Nat.cast_mul]

/-- Scalar multiplication at any fixed syntactic polynomial width is polynomial-time.

**Proof sketch.** Compose total projections, conversions and pairing with
`BinArith.polyTimeComputable_mul`, then the existing width writer. Read `mulPoly_eq`
for functional agreement; reuse the registered multiplication machinery. -/
theorem polyTimeComputable_mulPoly (p : PolyExpr) : PolyTimeComputable (mulPoly p) := by
  have ha : PolyTimeComputable
      (fun z => toLE (pairFstD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hb : PolyTimeComputable
      (fun z => toLE (pairSndD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have h : PolyTimeComputable (fun z =>
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.mul
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE (pairSndD (pairSndD z))))))) :=
    (polyTimeComputable_fromLEPoly p).comp
      (polyTimeComputable_pairFstD.pairEncode
        (BinArith.polyTimeComputable_mul.comp (ha.pairEncode hb)))
  exact (funext (mulPoly_eq p)).symm ▸ h

/-- Subtract the right inner operand modulo the power of two specified by the outer
template [PS10, Section 2.1, repository adaptation]. Reduce the right operand first
and add the modulus to the left operand before natural subtraction, avoiding underflow. -/
def subPoly (p : PolyExpr) (z : List Bool) : List Bool :=
  fromLEPoly p
    (pairEncode (pairFstD z)
      (BinArith.sub
        (pairEncode
          (BinArith.add
            (pairEncode
              (toLE (pairFstD (pairSndD z)))
              (toLE
                ([true] ++ List.replicate (p.eval (pairFstD z).length) false))))
          (toLE
            (normalizeWidthPoly p
              (pairEncode (pairFstD z) (pairSndD (pairSndD z))))))))

/-- `subPoly` normalizes the right operand, adds the binary modulus word to the left
operand, applies the existing natural subtractor, and writes the requested low bits. -/
theorem subPoly_eq (p : PolyExpr) (z : List Bool) :
    subPoly p z =
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.sub
            (pairEncode
              (BinArith.add
                (pairEncode
                  (toLE (pairFstD (pairSndD z)))
                  (toLE
                    ([true] ++ List.replicate (p.eval (pairFstD z).length) false))))
              (toLE
                (normalizeWidthPoly p
                  (pairEncode (pairFstD z) (pairSndD (pairSndD z)))))))) := rfl

/-- On a nested encoded pair, subtraction writes `A + q - (B mod q)` at width
`p.eval u.length`, where `q` is the corresponding power of two. This is an unconditional
formula for all operand lengths, rather than natural subtraction of the raw values.

**Proof sketch.** Read the own equation and pair projections. The MSB word consisting
of one followed by the polynomial zero word reads as the modulus, using the public
append, singleton and zero-word equations. The right normalizer reads as the right
value modulo that modulus. Convert operands to canonical LE bits, apply the public
addition/subtraction pair equations, and read the outer writer. -/
theorem subPoly_pairEncode (p : PolyExpr) (u a b : List Bool) :
    subPoly p (pairEncode u (pairEncode a b)) =
      Candidates.natToList (p.eval u.length)
        (listToNat a + 2 ^ (p.eval u.length) -
          (listToNat b % 2 ^ (p.eval u.length))) := by
  have hmodulus :
      listToNat ([true] ++ List.replicate (p.eval u.length) false) =
        2 ^ (p.eval u.length) := by
    rw [NumberTheory.listToNat_append, NumberTheory.listToNat_singleton_true,
      List.length_replicate, Candidates.listToNat_replicate_false,
      Nat.one_mul, Nat.add_zero]
  simp only [subPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    normalizeWidthPoly_pairEncode, toLE_eq_natBits,
    Candidates.listToNat_natToList_eq_mod, hmodulus,
    BinArith.add_pairEncode, BinArith.sub_pairEncode,
    fromLEPoly_pairEncode, LogProg.bitsVal_bits]

/-- Modular subtraction produces exactly the requested width on every raw input.

**Proof sketch.** Read `subPoly_eq`, apply `fromLEPoly_length`, and read the first
projection of the reconstructed pair. Zero width requires no special premise. -/
theorem subPoly_length (p : PolyExpr) (z : List Bool) :
    (subPoly p z).length = p.eval (pairFstD z).length := by
  rw [subPoly_eq, fromLEPoly_length, pairFstD_pairEncode]

/-- The subtraction output represents the ring difference modulo `2^(p.eval u.length)`
for arbitrary operands, including overlong words and width zero.

**Proof sketch.** Apply the canonical writer and remainder-reading equations. The
right remainder is strictly smaller than the positive modulus, so it is at most the
left value plus the modulus. Apply the natural subtraction cast under that bound;
`ZMod.natCast_self` removes the added modulus and `ZMod.natCast_mod` removes the right
remainder. This yields the ring difference without a fit premise. -/
theorem subPoly_natCast_pairEncode (p : PolyExpr) (u a b : List Bool) :
    (listToNat (subPoly p (pairEncode u (pairEncode a b))) :
        ZMod (2 ^ (p.eval u.length))) =
      (listToNat a : ZMod (2 ^ (p.eval u.length))) -
        (listToNat b : ZMod (2 ^ (p.eval u.length))) := by
  have hbound :
      listToNat b % 2 ^ (p.eval u.length) ≤
        listToNat a + 2 ^ (p.eval u.length) :=
    (Nat.mod_lt _ (Nat.two_pow_pos _)).le.trans (Nat.le_add_left _ _)
  rw [subPoly_pairEncode, Candidates.listToNat_natToList_eq_mod,
    ZMod.natCast_mod, Nat.cast_sub hbound, Nat.cast_add,
    ZMod.natCast_self, ZMod.natCast_mod, add_zero]

/-- Modular subtraction at any fixed syntactic polynomial width is polynomial-time.

**Proof sketch.** Generate the modulus word by appending a polynomial zero word to
the constant singleton `[true]`, using the existing zeros, constant and append contracts.
Compose conversions, pairing, the proved right normalizer and the existing arithmetic
machines with the width writer. Read `subPoly_eq`. The modulus has polynomial bit
length; no unary modulus, runtime polynomial evaluator or new host is introduced. -/
theorem polyTimeComputable_subPoly (p : PolyExpr) : PolyTimeComputable (subPoly p) := by
  have hzeros : PolyTimeComputable
      (fun z => List.replicate (p.eval (pairFstD z).length) false) :=
    EnsembleLemmas.polyTimeComputable_zeros p polyTimeComputable_pairFstD
  have hq : PolyTimeComputable
      (fun z => toLE
        ([true] ++ List.replicate (p.eval (pairFstD z).length) false)) :=
    polyTimeComputable_toLE.comp
      ((polyTimeComputable_const [true]).append hzeros)
  have ha : PolyTimeComputable
      (fun z => toLE (pairFstD (pairSndD z))) :=
    polyTimeComputable_toLE.comp
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have hb : PolyTimeComputable
      (fun z => toLE
        (normalizeWidthPoly p
          (pairEncode (pairFstD z) (pairSndD (pairSndD z))))) :=
    polyTimeComputable_toLE.comp
      ((polyTimeComputable_normalizeWidthPoly p).comp
        (polyTimeComputable_pairFstD.pairEncode
          (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)))
  have hcalc := BinArith.polyTimeComputable_sub.comp
    ((BinArith.polyTimeComputable_add.comp (ha.pairEncode hq)).pairEncode hb)
  have h : PolyTimeComputable (fun z =>
      fromLEPoly p
        (pairEncode (pairFstD z)
          (BinArith.sub
            (pairEncode
              (BinArith.add
                (pairEncode
                  (toLE (pairFstD (pairSndD z)))
                  (toLE
                    ([true] ++ List.replicate (p.eval (pairFstD z).length) false))))
              (toLE
                (normalizeWidthPoly p
                  (pairEncode (pairFstD z) (pairSndD (pairSndD z))))))))) :=
    (polyTimeComputable_fromLEPoly p).comp
      (polyTimeComputable_pairFstD.pairEncode hcalc)
  exact (funext (subPoly_eq p)).symm ▸ h

end TCSlib.Cryptography.Encoding.DyadicArithmetic
```


## ===== TCSlib/Cryptography/Encoding/DyadicLinearAlgebra.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.DyadicArithmetic
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Encoded dyadic dot products and matrix-vector multiplication

## Main definitions

* `dotStep`, `dotWords`, `dotPoly`: consume fixed-width blocks in the existing counted loop.
* `matVecStep`, `matVecPoly`: consume row-major matrix rows with that same public host.

## Main results

Raw output widths are unconditional. Canonical encodings correspond to modular dot
products and matrix-vector multiplication. The dot leaf step is polynomial-time.
The efficiency proofs compose the registered counted loop with the existing word operations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (machine representations).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2009,
  Section 7.2 (polynomial-time randomized computation, model context).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definitions 4.1.1 and 4.2.3 (the modular products being represented).

These algorithms are repository adaptations assembled from scalar arithmetic and
`Complexity.BinArith.forLoop`; no new traversal host is defined. Counters and retained
width words have explicit polynomial lengths. Short raw final blocks are read as their
ordinary MSB numeral, hence with implicit leading zeros; this is not a claim that the
flat operand is padded at its end. Malformed pairs use the existing total projections.
-/

namespace TCSlib.Cryptography.Encoding.DyadicLinearAlgebra

open Complexity Turing
open DyadicArithmetic

/-- Consume one coordinate pair and update the modular accumulator, retaining the
width word. This is the leaf step for the public counted-loop dot product. -/
def dotStep (z : List Bool) : List Bool :=
  let c := pairFstD z
  let xs := pairFstD (pairSndD z)
  let ys := pairFstD (pairSndD (pairSndD z))
  let acc := pairSndD (pairSndD (pairSndD z))
  pairEncode c (pairEncode (xs.drop c.length)
    (pairEncode (ys.drop c.length)
      (addPoly .var (pairEncode c (pairEncode acc
        (mulPoly .var (pairEncode c
          (pairEncode (xs.take c.length) (ys.take c.length)))))))))

/-- The complete step drops one width block per operand and adds their modular product. -/
theorem dotStep_eq (z : List Bool) :
    dotStep z =
      let c := pairFstD z
      let xs := pairFstD (pairSndD z)
      let ys := pairFstD (pairSndD (pairSndD z))
      let acc := pairSndD (pairSndD (pairSndD z))
      pairEncode c (pairEncode (xs.drop c.length)
        (pairEncode (ys.drop c.length)
          (addPoly .var (pairEncode c (pairEncode acc
            (mulPoly .var (pairEncode c
              (pairEncode (xs.take c.length) (ys.take c.length))))))))) := rfl

/-- The dot step preserves its entire width context, including on malformed input.

**Proof sketch.** Read the complete step equation and the public pair-first equation. -/
theorem dotStep_fst (z : List Bool) : pairFstD (dotStep z) = pairFstD z := by
  rw [dotStep_eq, pairFstD_pairEncode]

/-- One dot step grows by at most eight times the width-context size plus one.

**Proof sketch.** The two operands only shrink. Scalar arithmetic writes exactly the
retained width, even on malformed data. Expand public pairing lengths and bound any
framing repair by the stated slack; no numeric operand value enters the bound. -/
theorem dotStep_length_le (z : List Bool) :
    (dotStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  have houter := length_pair_components_le z
  have hmiddle := length_pair_components_le (pairSndD z)
  have hinner := length_pair_components_le (pairSndD (pairSndD z))
  simp only [dotStep_eq, length_pairEncode, List.length_drop, addPoly_length,
    pairFstD_pairEncode, PolyExpr.eval_var]
  omega

/-- The dot-product leaf step is polynomial-time, with no runtime polynomial argument.

**Proof sketch.** Compose total projections, `pairTakePoly .var` and
`pairDropPoly .var`, pairing,
and the already proved scalar `addPoly .var` and `mulPoly .var` contracts. The width
template is the retained word itself, so the per-step output bound is linear in it. -/
theorem polyTimeComputable_dotStep : PolyTimeComputable dotStep := by
  have hc := polyTimeComputable_pairFstD
  have hx := BinArith.polyTimeComputable_slot2
  have hy := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hacc := BinArith.polyTimeComputable_slot4
  have hxTake := (polyTimeComputable_pairTakePoly .var).comp (hc.pairEncode hx)
  have hyTake := (polyTimeComputable_pairTakePoly .var).comp (hc.pairEncode hy)
  have hxDrop := (polyTimeComputable_pairDropPoly .var).comp (hc.pairEncode hx)
  have hyDrop := (polyTimeComputable_pairDropPoly .var).comp (hc.pairEncode hy)
  have hproduct := (polyTimeComputable_mulPoly .var).comp
    (hc.pairEncode (hxTake.pairEncode hyTake))
  have hsum := (polyTimeComputable_addPoly .var).comp
    (hc.pairEncode (hacc.pairEncode hproduct))
  convert hc.pairEncode (hxDrop.pairEncode (hyDrop.pairEncode hsum)) using 1
  funext z
  simp only [dotStep_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- Run one dot step per letter of `n`, starting with a zero accumulator of width `|c|`.
Only the lengths of the two template words are used. -/
def dotWords (c n x y : List Bool) : List Bool :=
  let init := pairEncode c (pairEncode x (pairEncode y (List.replicate c.length false)))
  let done := pairSndD (BinArith.forLoop dotStep (pairEncode n init))
  pairSndD (pairSndD (pairSndD done))

/-- The complete dot loop initializes width-many zeros and extracts the final accumulator. -/
theorem dotWords_eq (c n x y : List Bool) :
    dotWords c n x y =
      let init := pairEncode c (pairEncode x (pairEncode y (List.replicate c.length false)))
      let done := pairSndD (BinArith.forLoop dotStep (pairEncode n init))
      pairSndD (pairSndD (pairSndD done)) := rfl

/-- The dot loop always writes exactly the width word's length.

**Proof sketch.** At zero iterations the initialized accumulator has that length.
Each later step replaces it with the fixed-width scalar sum. Use the public counted
loop equation, including when the count or width is zero. -/
theorem dotWords_length (c n x y : List Bool) : (dotWords c n x y).length = c.length := by
  let init := pairEncode c (pairEncode x (pairEncode y (List.replicate c.length false)))
  have h (k : ℕ) :
      pairFstD ((dotStep^[k]) init) = c ∧
      (pairSndD (pairSndD (pairSndD ((dotStep^[k]) init)))).length = c.length := by
    induction k with
    | zero => simp [init]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨(dotStep_fst _).trans ih.1, ?_⟩
      simp only [dotStep_eq, pairSndD_pairEncode, addPoly_length,
        pairFstD_pairEncode, PolyExpr.eval_var, ih.1]
  simp only [dotWords_eq, BinArith.forLoop_pairEncode, pairSndD_pairEncode]
  exact (h n.length).2

/-- The packed four-argument dot loop is polynomial-time on all raw words.

**Proof sketch.** Apply `forLoop_bound_of_ctx 8` to the retained-context and growth
lemmas, then `polyTimeComputable_forLoop` with envelope constants nine and two.
Initialize zeros and compose the final projections with the existing FP calculus. -/
theorem polyTimeComputable_dotWords : PolyTimeComputable
    (fun z => dotWords (pairFstD z) (pairFstD (pairSndD z))
      (pairFstD (pairSndD (pairSndD z))) (pairSndD (pairSndD (pairSndD z)))) := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_dotStep 9 2
    (BinArith.forLoop_bound_of_ctx 8 dotStep_fst dotStep_length_le)
  have hc := polyTimeComputable_pairFstD
  have hn := BinArith.polyTimeComputable_slot2
  have hx := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hy := BinArith.polyTimeComputable_slot4
  have hzero := EnsembleLemmas.polyTimeComputable_zeros .var hc
  have hinit := hc.pairEncode (hx.pairEncode (hy.pairEncode hzero))
  have hcomposed := (polyTimeComputable_pairSndD.comp BinArith.polyTimeComputable_slot4).comp
    (hloop.comp (hn.pairEncode hinit))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [dotWords_eq, Function.comp_apply, PolyExpr.eval_var]

/-- Fix polynomial coordinate and residue-width schedules before selecting a dot machine. -/
def dotPoly (N W : PolyExpr) (z : List Bool) : List Bool :=
  dotWords (List.replicate (W.eval (pairFstD z).length) false)
    (List.replicate (N.eval (pairFstD z).length) true)
    (pairFstD (pairSndD z)) (pairSndD (pairSndD z))

/-- The complete wrapper derives both loop templates from the parameter word's length. -/
theorem dotPoly_eq (N W : PolyExpr) (z : List Bool) :
    dotPoly N W z =
      dotWords (List.replicate (W.eval (pairFstD z).length) false)
        (List.replicate (N.eval (pairFstD z).length) true)
        (pairFstD (pairSndD z)) (pairSndD (pairSndD z)) := rfl

/-- The polynomial dot wrapper has its declared width on every raw input.

**Proof sketch.** Apply `dotWords_length` and the public replicate-length equation. -/
theorem dotPoly_length (N W : PolyExpr) (z : List Bool) :
    (dotPoly N W z).length = W.eval (pairFstD z).length := by
  simp only [dotPoly_eq, dotWords_length, List.length_replicate]

/-- On canonical full-width vectors the loop writes their modular inner product
[Pei16, Definitions 4.1.1 and 4.2.3, representation correspondence].

**Proof sketch.** Induct over the counted coordinates. Read `Modular.encodeVector_eq`
and use public list flatten/drop/take equations for the next canonical blocks;
scalar multiplication and addition preserve the running
sum in `ZMod q`. At termination the accumulator is the canonical fixed-width numeral. -/
theorem dotPoly_encodeVector {q : ℕ} [NeZero q] (N W : PolyExpr) (u : List Bool)
    (hq : q = 2 ^ (W.eval u.length))
    (a b : Fin (N.eval u.length) → ZMod q) :
    dotPoly N W (pairEncode u
      (pairEncode (Modular.encodeVector (W.eval u.length) a)
        (Modular.encodeVector (W.eval u.length) b))) =
      Candidates.natToList (W.eval u.length) (∑ i, a i * b i).val := by
  let width := W.eval u.length
  let c := List.replicate width false
  let numeral (x : ZMod q) := Candidates.natToList width x.val
  have hlength (x : ZMod q) : (numeral x).length = c.length := by
    simp only [numeral, Candidates.length_natToList, c, List.length_replicate]
  have hread (x : ZMod q) : NumberTheory.listToNat (numeral x) = x.val :=
    Candidates.listToNat_natToList (by rw [show 2 ^ width = q from hq.symm]; exact ZMod.val_lt x)
  have hmul (x y : ZMod q) :
      mulPoly .var (pairEncode c (pairEncode (numeral x) (numeral y))) = numeral (x * y) := by
    simp only [mulPoly_pairEncode, hread, PolyExpr.eval_var, c, List.length_replicate]
    dsimp only [numeral]
    rw [ZMod.val_mul, congrArg (fun modulus => x.val * y.val % modulus) hq,
      Candidates.natToList_mod_two_pow]
  have hadd (x y : ZMod q) :
      addPoly .var (pairEncode c (pairEncode (numeral x) (numeral y))) = numeral (x + y) := by
    simp only [addPoly_pairEncode, hread, PolyExpr.eval_var, c, List.length_replicate]
    dsimp only [numeral]
    rw [ZMod.val_add, congrArg (fun modulus => (x.val + y.val) % modulus) hq,
      Candidates.natToList_mod_two_pow]
  have hzero : List.replicate width false = numeral 0 := by
    simpa only [numeral, ZMod.val_zero, List.length_replicate,
      Candidates.listToNat_replicate_false] using
      (Candidates.natToList_length_listToNat (List.replicate width false)).symm
  have walk (k : ℕ) (x y : Fin k → ZMod q) (acc : ZMod q) :
      (dotStep^[k]) (pairEncode c (pairEncode (Modular.encodeVector width x)
          (pairEncode (Modular.encodeVector width y) (numeral acc)))) =
        pairEncode c (pairEncode [] (pairEncode [] (numeral (acc + ∑ i, x i * y i)))) := by
    induction k generalizing acc with
    | zero => simp [Modular.encodeVector_eq]
    | succ k ih =>
      have hsplit (v : Fin (k + 1) → ZMod q) : Modular.encodeVector width v =
          numeral (v 0) ++ Modular.encodeVector width (fun i : Fin k => v i.succ) := by
        rw [Modular.encodeVector_eq, List.ofFn_succ, List.flatten_cons, Modular.encodeVector_eq]
      rw [Function.iterate_succ_apply, dotStep_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, hsplit,
        List.drop_left' (hlength (x 0)), List.drop_left' (hlength (y 0)),
        List.take_left' (hlength (x 0)), List.take_left' (hlength (y 0)), hmul, hadd]
      rw [ih, Fin.sum_univ_succ, add_assoc]
  simp only [dotPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode, dotWords_eq,
    BinArith.forLoop_pairEncode, List.length_replicate]
  change pairSndD (pairSndD (pairSndD ((dotStep^[N.eval u.length])
    (pairEncode c (pairEncode (Modular.encodeVector width a)
      (pairEncode (Modular.encodeVector width b) (List.replicate width false))))))) = _
  rw [hzero, walk]
  simp only [pairSndD_pairEncode, zero_add, numeral, width]

/-- Every fixed polynomial dot schedule has a polynomial-time implementation.

**Proof sketch.** Generate the width template with the existing polynomial
zero-word machine and the counter with `polyTimeComputable_unaryPoly`, then compose the
packed `dotWords` machine. The polynomials are fixed outside the machine choice. -/
theorem polyTimeComputable_dotPoly (N W : PolyExpr) : PolyTimeComputable (dotPoly N W) := by
  have hc := EnsembleLemmas.polyTimeComputable_zeros W polyTimeComputable_pairFstD
  have hn := (polyTimeComputable_unaryPoly N).comp polyTimeComputable_pairFstD
  have hx := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hy := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hcomposed := polyTimeComputable_dotWords.comp (hc.pairEncode (hn.pairEncode (hx.pairEncode hy)))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [dotPoly_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Consume one matrix row, append its modular dot product, and retain width, column
count and the full input vector as the outer loop's context. -/
def matVecStep (z : List Bool) : List Bool :=
  let ctx := pairFstD z
  let c := pairFstD ctx
  let n := pairFstD (pairSndD ctx)
  let v := pairSndD (pairSndD ctx)
  let rows := pairFstD (pairSndD z)
  let out := pairSndD (pairSndD z)
  let rowWidth := n.length * c.length
  pairEncode ctx (pairEncode (rows.drop rowWidth)
    (out ++ dotWords c n (rows.take rowWidth) v))

/-- The complete row step uses a row of `|n|*|c|` bits and appends one width-sized result. -/
theorem matVecStep_eq (z : List Bool) :
    matVecStep z =
      let ctx := pairFstD z
      let c := pairFstD ctx
      let n := pairFstD (pairSndD ctx)
      let v := pairSndD (pairSndD ctx)
      let rows := pairFstD (pairSndD z)
      let out := pairSndD (pairSndD z)
      let rowWidth := n.length * c.length
      pairEncode ctx (pairEncode (rows.drop rowWidth)
        (out ++ dotWords c n (rows.take rowWidth) v)) := rfl

/-- The outer row step preserves its entire vector-and-dimension context.

**Proof sketch.** Read the step equation and the public pair-first equation. -/
theorem matVecStep_fst (z : List Bool) : pairFstD (matVecStep z) = pairFstD z := by
  rw [matVecStep_eq, pairFstD_pairEncode]

/-- One row step has linear growth in its retained context size.

**Proof sketch.** The matrix suffix only shrinks and the output grows by exactly
the width, using `dotWords_length`. Public pairing lengths cover malformed framing
with the stated constant slack. -/
theorem matVecStep_length_le (z : List Bool) :
    (matVecStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  have houter := length_pair_components_le z
  have hinner := length_pair_components_le (pairSndD z)
  have hwidth := length_pairFstD_le (pairFstD z)
  simp only [matVecStep_eq, length_pairEncode, List.length_drop, List.length_append,
    dotWords_length]
  omega

/-- The matrix row step is polynomial-time using the existing public loop host.

**Proof sketch.** Obtain the row-cut template with the public unary multiplication
machine `BinArith.mulU`, whose length is `|n|*|c|`. Compose `pairTakePoly .var`
and `pairDropPoly .var` on that row template,
the packed dot loop, append and total projections. No matrix traversal is rebuilt. -/
theorem polyTimeComputable_matVecStep : PolyTimeComputable matVecStep := by
  have hctx := polyTimeComputable_pairFstD
  have hctxTail := polyTimeComputable_pairSndD.comp hctx
  have hc := polyTimeComputable_pairFstD.comp hctx
  have hn := polyTimeComputable_pairFstD.comp hctxTail
  have hv := polyTimeComputable_pairSndD.comp hctxTail
  have hrows := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hout := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have htemplate := BinArith.polyTimeComputable_mulU.comp (hn.pairEncode hc)
  have hpair := htemplate.pairEncode hrows
  have hrow := (polyTimeComputable_pairTakePoly .var).comp hpair
  have hrest := (polyTimeComputable_pairDropPoly .var).comp hpair
  have hvalue := polyTimeComputable_dotWords.comp (hc.pairEncode (hn.pairEncode (hrow.pairEncode hv)))
  have hcomposed := hctx.pairEncode (hrest.pairEncode (hout.append hvalue))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [matVecStep_eq, Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var, BinArith.length_mulU]

/-- Multiply a row-major matrix by a vector using fixed polynomial row, column and
residue-width schedules and the existing counted-loop host. -/
def matVecPoly (M N W : PolyExpr) (z : List Bool) : List Bool :=
  let u := pairFstD z
  let c := List.replicate (W.eval u.length) false
  let n := List.replicate (N.eval u.length) true
  let ctx := pairEncode c (pairEncode n (pairSndD (pairSndD z)))
  let init := pairEncode ctx (pairEncode (pairFstD (pairSndD z)) [])
  let done := pairSndD (BinArith.forLoop matVecStep
    (pairEncode (List.replicate (M.eval u.length) true) init))
  pairSndD (pairSndD done)

/-- The complete wrapper initializes an empty output and runs one step per declared row. -/
theorem matVecPoly_eq (M N W : PolyExpr) (z : List Bool) :
    matVecPoly M N W z =
      let u := pairFstD z
      let c := List.replicate (W.eval u.length) false
      let n := List.replicate (N.eval u.length) true
      let ctx := pairEncode c (pairEncode n (pairSndD (pairSndD z)))
      let init := pairEncode ctx (pairEncode (pairFstD (pairSndD z)) [])
      let done := pairSndD (BinArith.forLoop matVecStep
        (pairEncode (List.replicate (M.eval u.length) true) init))
      pairSndD (pairSndD done) := rfl

/-- The matrix wrapper writes exactly row-count times width bits on every raw input.

**Proof sketch.** The initialized output is empty and each counted row appends exactly
the retained width by `dotWords_length`. No positive width or column count is needed. -/
theorem matVecPoly_length (M N W : PolyExpr) (z : List Bool) :
    (matVecPoly M N W z).length =
      M.eval (pairFstD z).length * W.eval (pairFstD z).length := by
  let u := pairFstD z
  let c := List.replicate (W.eval u.length) false
  let n := List.replicate (N.eval u.length) true
  let ctx := pairEncode c (pairEncode n (pairSndD (pairSndD z)))
  let init := pairEncode ctx (pairEncode (pairFstD (pairSndD z)) [])
  have h (k : ℕ) :
      pairFstD ((matVecStep^[k]) init) = ctx ∧
      (pairSndD (pairSndD ((matVecStep^[k]) init))).length = k * c.length := by
    induction k with
    | zero => simp [init]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨(matVecStep_fst _).trans ih.1, ?_⟩
      simp only [matVecStep_eq, pairSndD_pairEncode, List.length_append, dotWords_length,
        ih.1, ih.2, ctx, pairFstD_pairEncode, Nat.succ_mul]
  simp only [matVecPoly_eq, BinArith.forLoop_pairEncode, List.length_replicate, pairSndD_pairEncode]
  simpa only [u, c, List.length_replicate] using (h (M.eval u.length)).2

/-- On canonical inputs the matrix loop writes the existing modular matrix-vector product
[Pei16, Definition 4.2.3, representation correspondence].

**Proof sketch.** Induct over the outer counted rows and apply `dotPoly`'s inner-loop
invariant to each exact row. Concatenating the fixed-width results is precisely the
public vector encoder. Empty rows, columns and width are handled by the counters. -/
theorem matVecPoly_encodeMatrix {q : ℕ} [NeZero q] (M N W : PolyExpr) (u : List Bool)
    (hq : q = 2 ^ (W.eval u.length))
    (A : Matrix (Fin (M.eval u.length)) (Fin (N.eval u.length)) (ZMod q))
    (v : Fin (N.eval u.length) → ZMod q) :
    matVecPoly M N W (pairEncode u
      (pairEncode (Modular.encodeMatrix (W.eval u.length) A)
        (Modular.encodeVector (W.eval u.length) v))) =
      Modular.encodeVector (W.eval u.length) (A.mulVec v) := by
  let width := W.eval u.length
  let c := List.replicate width false
  let n := List.replicate (N.eval u.length) true
  let ctx := pairEncode c (pairEncode n (Modular.encodeVector width v))
  have hdot (row : Fin (N.eval u.length) → ZMod q) :
      dotWords c n (Modular.encodeVector width row) (Modular.encodeVector width v) =
        Candidates.natToList width (∑ i, row i * v i).val := by
    simpa only [dotPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode] using
      dotPoly_encodeVector N W u hq row v
  have walk (k : ℕ) (rows : Matrix (Fin k) (Fin (N.eval u.length)) (ZMod q)) (out : List Bool) :
      (matVecStep^[k]) (pairEncode ctx (pairEncode (Modular.encodeMatrix width rows) out)) =
        pairEncode ctx (pairEncode [] (out ++ Modular.encodeVector width (rows.mulVec v))) := by
    induction k generalizing out with
    | zero => simp [Modular.encodeMatrix_eq, Modular.encodeVector_eq]
    | succ k ih =>
      let tail : Matrix (Fin k) (Fin (N.eval u.length)) (ZMod q) := fun i j => rows i.succ j
      have hsplit : Modular.encodeMatrix width rows =
          Modular.encodeVector width (rows 0) ++ Modular.encodeMatrix width tail := by
        rw [Modular.encodeMatrix_eq, List.ofFn_succ, List.flatten_cons, Modular.encodeMatrix_eq]
      have hresult : Modular.encodeVector width (rows.mulVec v) =
          Candidates.natToList width (∑ i, rows 0 i * v i).val ++
            Modular.encodeVector width (tail.mulVec v) := by
        simp only [Modular.encodeVector_eq, List.ofFn_succ, List.flatten_cons]
        rfl
      have hrow : (Modular.encodeVector width (rows 0)).length = n.length * c.length := by
        simp only [Modular.encodeVector_length, n, c, List.length_replicate]
      rw [Function.iterate_succ_apply, matVecStep_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, ctx, hsplit,
        List.drop_left' hrow, List.take_left' hrow, hdot]
      rw [ih, hresult, List.append_assoc]
  simp only [matVecPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.forLoop_pairEncode, List.length_replicate]
  change pairSndD (pairSndD ((matVecStep^[M.eval u.length])
    (pairEncode ctx (pairEncode (Modular.encodeMatrix width A) [])))) = _
  rw [walk]
  simp only [pairSndD_pairEncode, List.nil_append, width]

/-- Every fixed polynomial matrix-vector schedule has a polynomial-time implementation.

**Proof sketch.** Apply the public retained-context loop envelope with constant eight
to `matVecStep`, obtaining the nine/two polynomial bound. Generate the fixed schedule
templates with existing polynomial unary-word machines and compose final projections. -/
theorem polyTimeComputable_matVecPoly (M N W : PolyExpr) :
    PolyTimeComputable (matVecPoly M N W) := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_matVecStep 9 2
    (BinArith.forLoop_bound_of_ctx 8 matVecStep_fst matVecStep_length_le)
  have hu := polyTimeComputable_pairFstD
  have hc := EnsembleLemmas.polyTimeComputable_zeros W hu
  have hn := (polyTimeComputable_unaryPoly N).comp hu
  have hm := (polyTimeComputable_unaryPoly M).comp hu
  have hctx := hc.pairEncode (hn.pairEncode BinArith.polyTimeComputable_slot3)
  have hinit := hctx.pairEncode
    (BinArith.polyTimeComputable_slot2.pairEncode (polyTimeComputable_const []))
  have hcomposed := BinArith.polyTimeComputable_slot4.comp
    (hloop.comp (hm.pairEncode hinit))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [matVecPoly_eq, Function.comp_apply]

end TCSlib.Cryptography.Encoding.DyadicLinearAlgebra
```


## ===== TCSlib/Cryptography/Foundations/Negligible.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Negligible and noticeable functions

A function of the security parameter is negligible when it eventually falls below every
inverse polynomial, and noticeable when it eventually stays above some inverse
polynomial. Security definitions allow an adversary negligible success; hardness
amplification starts from a noticeable failure probability. The two notions are not
complementary: a function can be neither.

The functions here take real values and the conditions bound `|μ n|`, so that
differences of probabilities can be fed in directly. [Gar26] restricts to values in
`[0, 1]`; on such functions the definitions agree.

## Main definitions

* `Negligible μ`: for every `c`, eventually `|μ n| < 1 / n^c`.
* `Noticeable μ`: for some `c`, eventually `μ n > 1 / n^c`.

## Main results

* `Negligible.add`, `Negligible.mul`, `Negligible.const_mul`, `Negligible.mono`: closure.
* `Negligible.mul_pow`: a negligible function times a polynomial is negligible.
* `negligible_two_pow_neg`: `2^{-n}` is negligible; `negligible_zero`: so is the constant `0`.
* `Noticeable.not_negligible`: noticeable functions are not negligible.
* `not_negligible_sub`: a non-negligible function minus a negligible one is
  non-negligible.
* `exists_not_negligible_not_noticeable`: some function is neither.
* `not_negligible_iff`: a function is non-negligible exactly when it exceeds some
  inverse polynomial infinitely often.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §1.2 (Definitions 1.3 and 1.4, Exercise 1.1) and
  Exercises 2.1 and 2.2.
-/

namespace TCSlib.Cryptography

/-- A function `μ` of the security parameter is negligible when for every `c` there is
`n₀` with `|μ n| < 1 / n^c` for all `n ≥ n₀`. [Gar26, Definition 1.4], for real-valued
functions bounded in absolute value; on `[0, 1]`-valued functions this is the source's
definition. -/
def Negligible (μ : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |μ n| < 1 / (n : ℝ) ^ c

/-- The defining property of `Negligible`: `Negligible μ` iff for every `c` there is `n₀` with
`|μ n| < 1 / n^c` for all `n ≥ n₀`. -/
theorem negligible_iff (μ : ℕ → ℝ) :
    Negligible μ ↔ ∀ c : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, |μ n| < 1 / (n : ℝ) ^ c := Iff.rfl

/-- A function `μ` is noticeable when there are `c` and `n₀` with `μ n > 1 / n^c` for all
`n ≥ n₀`. [Gar26, Definition 1.3]. -/
def Noticeable (μ : ℕ → ℝ) : Prop :=
  ∃ c n₀ : ℕ, ∀ n ≥ n₀, 1 / (n : ℝ) ^ c < μ n

variable {μ ν : ℕ → ℝ}

/-- A function eventually dominated in absolute value by a negligible one is negligible.
Technical glue. -/
theorem Negligible.mono (hμ : Negligible μ) (h : ∃ n₀, ∀ n ≥ n₀, |ν n| ≤ |μ n|) :
    Negligible ν := by
  intro c
  obtain ⟨n₀, h₀⟩ := h
  obtain ⟨n₁, h₁⟩ := hμ c
  exact ⟨max n₀ n₁, fun n hn =>
    (h₀ n (le_of_max_le_left hn)).trans_lt (h₁ n (le_of_max_le_right hn))⟩

/-- The sum of two negligible functions is negligible. [Gar26, Exercise 1.1(1)–(2)].

**Proof sketch.** Bound each by `1 / n^(c+1)` eventually; their sum is below
`2 / n^(c+1) ≤ 1 / n^c` once `n ≥ 2`. -/
theorem Negligible.add (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n + ν n) := by
  intro c
  obtain ⟨n₁, h₁⟩ := hμ (c + 1)
  obtain ⟨n₂, h₂⟩ := hν (c + 1)
  refine ⟨max (max n₁ n₂) 2, fun n hn => ?_⟩
  have hn₁ : n ≥ n₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂ : n ≥ n₂ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ c := pow_pos (by linarith) c
  have key : 2 * (1 / (n : ℝ) ^ (c + 1)) ≤ 1 / (n : ℝ) ^ c := by
    have hinv : 1 / (n : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le two_pos h2
    have ha : 0 < 1 / (n : ℝ) ^ c := by positivity
    rw [pow_succ, ← one_div_mul_one_div]
    nlinarith
  calc |μ n + ν n| ≤ |μ n| + |ν n| := abs_add_le _ _
    _ < 1 / (n : ℝ) ^ (c + 1) + 1 / (n : ℝ) ^ (c + 1) := add_lt_add (h₁ n hn₁) (h₂ n hn₂)
    _ ≤ 1 / (n : ℝ) ^ c := by linarith

/-- The product of two negligible functions is negligible. [Gar26, Exercise 1.1(3) and
Exercise 2.1].

**Proof sketch.** Eventually `|ν n| < 1` (the bound for `c = 0`), so
`|μ n ν n| ≤ |μ n| < 1 / n^c`. -/
theorem Negligible.mul (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible (fun n => μ n * ν n) := by
  intro c
  obtain ⟨n₁, h₁⟩ := hμ c
  obtain ⟨n₂, h₂⟩ := hν 0
  refine ⟨max n₁ n₂, fun n hn => ?_⟩
  have hν1 : |ν n| < 1 := by simpa using h₂ n (le_of_max_le_right hn)
  rw [abs_mul]
  calc |μ n| * |ν n| ≤ |μ n| * 1 := mul_le_mul_of_nonneg_left hν1.le (abs_nonneg _)
    _ < 1 / (n : ℝ) ^ c := by rw [mul_one]; exact h₁ n (le_of_max_le_left hn)

/-- A negligible function times the polynomial `n^d` is negligible. Used whenever a
hybrid argument multiplies an advantage by a polynomial number of hybrids. [Gar26,
§1.2, "any polynomial function of a negligible function is still negligible"].

**Proof sketch.** Given `c`, use the bound for `c + d`. -/
theorem Negligible.mul_pow (hμ : Negligible μ) (d : ℕ) :
    Negligible (fun n => (n : ℝ) ^ d * μ n) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ (c + d)
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos (by linarith) d
  rw [abs_mul, abs_of_pos hpos]
  calc (n : ℝ) ^ d * |μ n| < (n : ℝ) ^ d * (1 / (n : ℝ) ^ (c + d)) :=
        mul_lt_mul_of_pos_left (h₀ n (le_of_max_le_left hn)) hpos
    _ = 1 / (n : ℝ) ^ c := by
        rw [pow_add]; field_simp

/-- A constant multiple of a negligible function is negligible. [Gar26, §1.2].

**Proof sketch.** For `n ≥ |a|`, `|a μ n| ≤ |n μ n|`, and `n μ n` is negligible by
`Negligible.mul_pow`. -/
theorem Negligible.const_mul (hμ : Negligible μ) (a : ℝ) :
    Negligible (fun n => a * μ n) := by
  refine (hμ.mul_pow 1).mono ⟨⌈|a|⌉₊, fun n hn => ?_⟩
  have ha : |a| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [abs_mul, abs_mul, pow_one, Nat.abs_cast]
  exact mul_le_mul_of_nonneg_right ha (abs_nonneg _)

/-- The function `2^{-n}` is negligible. [Gar26, §1.2, Example after Definition 1.4].

**Proof sketch.** `n^c < 2^n` for all large `n`. -/
theorem negligible_two_pow_neg : Negligible (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro c
  have ht := tendsto_pow_const_div_const_pow_of_one_lt c (r := (2 : ℝ)) one_lt_two
  obtain ⟨n₀, h₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds zero_lt_one))
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  have hlt : (n : ℝ) ^ c < 2 ^ n :=
    (div_lt_one (by positivity)).mp (h₀ n (le_of_max_le_left hn))
  show |(2 : ℝ)⁻¹ ^ n| < 1 / (n : ℝ) ^ c
  rw [abs_of_pos (by positivity), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt (pow_pos (by linarith) c) hlt

/-- The constant zero function is negligible: `|0| = 0 < 1 / n^c` for every `n ≥ 1`. Technical
glue (the advantage of a distinguisher between two equal distributions). Added by the
Pass–shelat campaign (gate 03a, ruling G3-7a), which moved it here from
`Asymptotic/Ensembles.lean` under its unchanged full name. -/
theorem negligible_zero : Negligible fun _ : ℕ => (0 : ℝ) := by
  intro c
  refine ⟨1, fun n hn => ?_⟩
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [abs_zero]
  positivity

/-- A noticeable function is not negligible. [Gar26, §1.2].

**Proof sketch.** With the noticeability exponent `c`, at any `n` past both thresholds
`1 / n^c < μ n ≤ |μ n| < 1 / n^c`. -/
theorem Noticeable.not_negligible (hμ : Noticeable μ) : ¬ Negligible μ := by
  intro hneg
  obtain ⟨c, n₀, h₀⟩ := hμ
  obtain ⟨n₁, h₁⟩ := hneg c
  have a := h₀ (max n₀ n₁) (le_max_left _ _)
  have b := h₁ (max n₀ n₁) (le_max_right _ _)
  linarith [le_abs_self (μ (max n₀ n₁))]

/-- A function is non-negligible exactly when there is `c` such that `|μ n| ≥ 1 / n^c`
for infinitely many `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"]. -/
theorem not_negligible_iff :
    ¬ Negligible μ ↔ ∃ c : ℕ, ∀ n₀ : ℕ, ∃ n ≥ n₀, 1 / (n : ℝ) ^ c ≤ |μ n| := by
  simp only [Negligible, not_forall, not_exists, not_lt, exists_prop]

/-- If `μ` is not negligible and `ν` is negligible then `μ - ν` is not negligible.
[Gar26, §2.2.2, footnote 3 (exercise)].

**Proof sketch.** Otherwise `μ = (μ - ν) + ν` would be negligible. -/
theorem not_negligible_sub (hμ : ¬ Negligible μ) (hν : Negligible ν) :
    ¬ Negligible (fun n => μ n - ν n) := by
  intro h
  exact hμ (by simpa using h.add hν)

/-- Some function into `[0, 1]` is neither negligible nor noticeable: `2^{-n}` at even
`n` and `n^{-3}` at odd `n`. [Gar26, §1.2, "Gap between Noticeable and Negligible
Functions"].

**Proof sketch.** The values lie in `[0, 1]` directly. At odd `n` the value is `1 / n^3`,
so the bound for `c = 3` fails infinitely often and `μ` is not negligible
(`not_negligible_iff`). At even `n` the value is `2^{-n}`, which is eventually below every
`1 / n^c` (`negligible_two_pow_neg`), so `μ` is not noticeable. -/
theorem exists_not_negligible_not_noticeable :
    ∃ μ : ℕ → ℝ, (∀ n, 0 ≤ μ n ∧ μ n ≤ 1) ∧ ¬ Negligible μ ∧ ¬ Noticeable μ := by
  refine ⟨fun n => if n % 2 = 0 then (2 : ℝ)⁻¹ ^ n else 1 / (n : ℝ) ^ 3, ?_, ?_, ?_⟩
  · intro n
    dsimp only
    split_ifs with h
    · exact ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      exact ⟨by positivity, div_le_one_of_le₀ (one_le_pow₀ hn) (by positivity)⟩
  · refine not_negligible_iff.mpr ⟨3, fun n₀ => ⟨2 * n₀ + 1, by omega, ?_⟩⟩
    dsimp only
    rw [if_neg (by omega)]
    exact le_abs_self _
  · rintro ⟨c, n₀, h₀⟩
    obtain ⟨n₁, h₁⟩ := negligible_two_pow_neg c
    have h := h₀ (2 * max n₀ n₁) (by omega)
    have h' := h₁ (2 * max n₀ n₁) (by omega)
    dsimp only at h h'
    rw [if_pos (by omega)] at h
    rw [abs_of_pos (by positivity)] at h'
    linarith

end TCSlib.Cryptography
```


## ===== TCSlib/Complexity/Randomized/PPT.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PolyExpr

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic polynomial-time machines, uniform and non-uniform

The randomized machine model of [PS10, §2.1]: the probabilistic polynomial-time Turing
machine (PPT) [PS10, Definition 23.4] with the worst-case running-time convention
[PS10, Definition 23.5], the notion "computes `f` with probability one"
[PS10, Definition 24.6], and the non-uniform PPT of [PS10, Definition 26.8] in its advice
formulation ("a uniform p.p.t. machine `A` that receives an advice string for each input
length"). One structure, `Complexity.NUPPT`, carries all of them (foundation decisions D3
and D4 of `PassShelatChapter2-4Plan.md`):

* a finite binary machine `M : Turing.FinTM Bool` that halts on **every** input `z` within
  `Ct * (|z| + 1) ^ ct` steps;
* an explicit coin polynomial `coins : PolyExpr` (`coins.eval n` uniform coins at parameter
  `n`) and an advice polynomial `adv : PolyExpr` with an advice function `advice : ℕ → List Bool`
  of length `≤ adv.eval n`;
* the single semantic primitive `output z` (the output tape when the budget expires), which is
  `PolyTimeComputable` (`NUPPT.polyTimeComputable_output`), and conversely every
  `PolyTimeComputable` function is the output of some `NUPPT` (`NUPPT.ofPolyTime`).

The activation at security parameter `n` on argument `y` with coins `r` is
`runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`
(pairs are `Turing.pairEncode`, `1^n = List.replicate n true`). The random tape is part of the
input, so the time bound holds for every coin string, which is exactly the worst-case
convention of [PS10, Definition 23.5]; "`A` computes `f` with probability 1"
[PS10, Definition 24.6] is `NUPPT.Computes`: equality for every coin string (on the finite
uniform coin space, probability one is the same as every coin string, see
`TCSlib.Cryptography.Asymptotic.Adversary`). A PPT [PS10, Definition 23.4] is an `NUPPT` with
empty advice (`NUPPT.Uniform`); `Complexity.PPT` is the subtype. `Computes` does not require
`Uniform`: [PS10, Definition 24.6] is about a randomized algorithm, i.e. a PPT, and is the case
`A.Uniform ∧ A.Computes f`; for a non-uniform `A`, `Computes` is the advice analogue and holds
for uncomputable `f` (advice `[h n]` for an arbitrary `h : ℕ → Bool`, read back by the machine).
So `∃ A : NUPPT, A.Computes f` does not say that a PPT computes `f`. Efficient computation of
`f` on the encodings `⟨1^n, y⟩` is `∃ A, A.Uniform ∧ A.Computes f`
(`NUPPT.exists_uniform_computes`, and conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which gives polynomial-time computability of
`z ↦ f ⟨1^{|fst z|}, snd z⟩`). `Computes` says nothing about `f` off those encodings, so it is
not [PS10, Definition 24.6] for an arbitrary `f : {0,1}* → {0,1}*`, which constrains every
input string (gate 03a, round 2, R2-1). The
input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8] is `NUPPT.runLit`; the
lemmas about it and about uniformity are in `TCSlib.Complexity.Randomized.NonUniform`.

## Deviations (DESIGN.md §5, items 1–2)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional
   module).

In detail (D3): a machine that is polynomial-time on well-formed inputs can be clocked by
`Turing.timed_universal` into one that halts on every input, so requiring totality does not
change the class of behaviours (the optional lemma `NUPPT.ofPartial` doing this is not needed
by any theorem of chapters 2–4); the time bound is measured in the length of the machine
input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`, a polynomial in `n + |y|`, so the classes "polynomial in
`n`" (for `|y|` polynomial in `n`, the only case the experiments produce) and "polynomial in
the machine input" coincide.

**Interdefinability of the `1^n`-indexed and the input-length-indexed forms (D3/D4).** The
text indexes advice and coins by the input length (`A_{|x|}(x)`), while `NUPPT` indexes
them by the parameter `n` read from the unary prefix `1^n`. The two are interdefinable in
every experiment of the text: (i) an `NUPPT` run at `n := |y|` is exactly the text's
`A_{|y|}(y)`, by definition (`NUPPT.runLit`; the prefix `1^{|y|}` carries no information);
(ii) conversely, every experiment of the text hands the adversary strings
whose length is a fixed polynomial `ℓ(n)` of the parameter, and an input-length-indexed
machine at length `ℓ(n)` becomes a `1^n`-indexed one by hard-wiring its advice at `ℓ(n)` and
evaluating its coin polynomial at `ℓ(n)` (`exists_reparam_advice` with `φ := ℓ.eval`); for
injective `ℓ` the converse hard-wires `1^n` into the advice at length `ℓ(n)`. The `1^n`
indexing is what makes one random tape per `n` well-typed for the oracle and interactive
layouts of chapters 3–4, where the machine is activated several times at one parameter on
inputs of varying length. Both forms are kept side by side where the text uses the literal
one (Definitions 26.1 and 69.4) and are related by explicit lemmas, never unified silently.

## Main definitions

* `Complexity.NUPPT` — non-uniform PPT [PS10, Definition 26.8, advice formulation]; a PPT
  [PS10, Definition 23.4] is the case `NUPPT.Uniform` (empty advice).
* `Complexity.NUPPT.output` — the output of the machine on a raw input (the semantic
  primitive); `NUPPT.timeBound`, `NUPPT.coinLen`, `NUPPT.adviceLen`.
* `Complexity.NUPPT.advInput` — the adversary input `⟨1^n, y⟩`; `NUPPT.Coins` — the coin type
  at parameter `n`; `NUPPT.runAt`, `NUPPT.runAtL`, `NUPPT.runLit` — activations.
* `Complexity.NUPPT.Uniform` — no advice (a PPT); `Complexity.PPT` — the subtype, with
  `PPT.toNUPPT`, `PPT.ofPolyTime` (readers `PPT.toNUPPT_mk`, `PPT.uniform`,
  `PPT.toNUPPT_ofPolyTime`).
* `Complexity.NUPPT.Computes` — computes `f` with probability one: [PS10, Definition 24.6] for a
  uniform `A` (`NUPPT.Uniform`), the advice analogue otherwise.
* `Complexity.NUPPT.ofPolyTime`, `Complexity.NUPPT.ofPolyTimeUniform` — the `NUPPT` with a
  given polynomial-time output function, with and without advice.

## Main results

* `Complexity.NUPPT.output_spec`, `NUPPT.computesFunInTime`,
  `NUPPT.polyTimeComputable_output` — the output function is computed by the machine within
  its budget, hence is polynomial-time computable.
* `Complexity.NUPPT.output_eq_of_computesInTime` — determinism: any completed computation of
  the machine names `output`.
* `Complexity.NUPPT.output_ofPolyTime`, `NUPPT.ofPolyTimeUniform_uniform` — the converse
  direction: `ofPolyTime hf` outputs `f`, and `ofPolyTimeUniform` is uniform.
* `Complexity.NUPPT.exists_uniform_computes` — every polynomial-time computable function is
  computed with probability one by a PPT [PS10, Definition 24.6, non-vacuity].
* `Complexity.NUPPT.nonempty` — the class is inhabited.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1: Definitions 23.4, 23.5, 24.6 and 26.8.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (Definition 1.3, time-bounded computation; §6.3, advice.)
-/

namespace Complexity

open Turing

/-- A non-uniform probabilistic polynomial-time machine [PS10, Definition 26.8, advice
formulation]: a finite binary machine halting on **every** input `z` within
`Ct (|z|+1)^ct` steps, the explicit polynomial `coins` giving the number of uniform coins at
parameter `n`, and an advice string of length at most `adv.eval n` per parameter.
A PPT [PS10, Definition 23.4] is the case of empty advice (`Uniform`); the time bound holds
for every coin string, the worst-case convention of [PS10, Definition 23.5].

**Deviation:** `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time
in the machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
**Deviation:** `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core
(optional module). -/
structure NUPPT where
  /-- The underlying deterministic finite machine; coins and advice are input components. -/
  M : FinTM Bool
  /-- Coefficient of the running-time bound `Ct * (|z| + 1) ^ ct`. -/
  Ct : ℕ
  /-- Degree of the running-time bound. -/
  ct : ℕ
  /-- The coin polynomial: `coins.eval n` uniform coins at parameter `n`. -/
  coins : PolyExpr
  /-- The advice polynomial: `|advice n| ≤ adv.eval n`. -/
  adv : PolyExpr
  /-- The advice string per parameter (empty for a uniform machine). -/
  advice : ℕ → List Bool
  /-- The advice is polynomially bounded. -/
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  /-- The machine halts on every input within its polynomial budget. -/
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT

variable (A : NUPPT)

/-- The running-time budget of `A` on inputs of length `m`: `Ct * (m + 1) ^ ct`. -/
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct

/-- The defining equation of `timeBound`: `timeBound m = A.Ct * (m + 1) ^ A.ct`. -/
theorem timeBound_def (m : ℕ) :
    timeBound A m =
      (A.Ct * (m + 1) ^ A.ct) := rfl

/-- The number of coins of `A` at parameter `n`. -/
def coinLen (n : ℕ) : ℕ := A.coins.eval n

/-- The defining equation of `coinLen`: `A.coinLen n = A.coins.eval n`. -/
theorem coinLen_eq (n : ℕ) : A.coinLen n = A.coins.eval n := rfl

/-- The advice-length bound of `A` at parameter `n`. -/
def adviceLen (n : ℕ) : ℕ := A.adv.eval n

/-- The output of `A` on the raw machine input `z`: the output tape when the budget expires
(the machine has halted by then, `output_spec`). This is the single semantic primitive; all
activations are instances of it. -/
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output

/-- The machine halts on `z` within its budget with `output z` on the output tape. -/
theorem output_spec (z : List Bool) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length) := by
  obtain ⟨out, h⟩ := A.halts z
  obtain ⟨hs, -⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  exact (FinTM.computesInTime_iff _ _ _ _).mpr ⟨hs, rfl⟩

/-- The machine computes the function `output` within the budget `timeBound`. -/
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound :=
  (FinTM.computesFunInTime_iff _ _ _).2 fun z => A.output_spec z

/-- The output function of an `NUPPT` is polynomial-time computable: the black box through
which every reduction of the campaign is exhibited as a machine (D2). -/
theorem polyTimeComputable_output : PolyTimeComputable A.output :=
  (polyTimeComputable_iff _).2 ⟨A.M, A.Ct, A.ct, A.computesFunInTime⟩

/-- Determinism: any completed computation of the machine on `z` produces `output z`
(`Turing.FinTM.ComputesInTime.output_unique`). -/
theorem output_eq_of_computesInTime {z w : List Bool} {t : ℕ} (h : A.M.ComputesInTime z w t) :
    A.output z = w :=
  (A.output_spec z).output_unique h

/-- The output is no longer than the budget (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem output_length_le (z : List Bool) : (A.output z).length ≤ A.timeBound z.length :=
  A.M.tm.output_length_le z (A.timeBound z.length)

/-- The adversary input `⟨1^n, y⟩`: the unary security parameter paired with the argument,
exactly as the text writes `A(1^n, y)` [PS10, Definition 27.3]. -/
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y

/-- The defining equation of `advInput`: `advInput n y = pairEncode (List.replicate n true) y`
(the pair `⟨1^n, y⟩`). -/
theorem advInput_eq (n : ℕ) (y : List Bool) :
    advInput n y = pairEncode (List.replicate n true) y := rfl

/-- The length of the adversary input `⟨1^n, y⟩` is `2n + 2 + |y|`. -/
theorem length_advInput (n : ℕ) (y : List Bool) : (advInput n y).length = 2 * n + 2 + y.length := by
  simp [advInput, length_pairEncode]

/-- The coin type of `A` at parameter `n`: `coins.eval n` uniform bits
[PS10, Definition 23.4, "each bit of the random tape is uniformly and independently chosen"]. -/
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool

/-- Activation at parameter `n` on argument `y` with coins `r`: machine input
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The sampler `r ↦ runAt n y r` on the uniform coin type
`Coins n` is the distribution `A(1^n, y)` of the text. -/
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))

/-- Activation with an untyped coin string (the interactive and oracle layouts of
chapters 3–4 hand the machine a coin string of the right length as a list). -/
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)

/-- The defining equation of `runAtL`:
`A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)`. -/
theorem runAtL_eq (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r) := rfl

/-- The typed activation is the untyped one on `List.ofFn r`. -/
theorem runAt_eq (n : ℕ) (y : List Bool) (r : A.Coins n) :
    A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl

/-- **The coins of two machines with the same coin polynomial**: `A.Coins n ≃ B.Coins n` when
`A.coins = B.coins` (`finCongr` on the coin lengths). A construction that keeps the coins of the
machine it is built from publishes its coin identification through it, so that consumers move
between the two coin types without reducing `coinLen` or the construction. -/
def coinsCongr {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) : A.Coins n ≃ B.Coins n :=
  Equiv.arrowCongr (finCongr (by rw [coinLen_eq, coinLen_eq, h])) (Equiv.refl Bool)

/-- The coin equivalence keeps the coin string: `List.ofFn (coinsCongr h n r) = List.ofFn r`. -/
theorem coinsCongr_ofFn {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) (r : A.Coins n) :
    List.ofFn (coinsCongr h n r) = List.ofFn r :=
  (List.ofFn_congr (by rw [coinLen_eq, coinLen_eq, h]) r).symm

/-- Running `B` on coins carried over from `A`: `B.runAt n y (coinsCongr h n r) =
B.runAtL n y (List.ofFn r)`. -/
theorem runAt_coinsCongr {A B : NUPPT} (h : A.coins = B.coins) (n : ℕ) (y : List Bool)
    (r : A.Coins n) : B.runAt n y (coinsCongr h n r) = B.runAtL n y (List.ofFn r) := by
  rw [runAt_eq, coinsCongr_ofFn]

/-- **The coins of a machine with a known coin polynomial**: `A.Coins n ≃ {0,1}^{c(n)}` when
`A.coins = c` (`finCongr` on the coin length). The interface through which a statement reads the
coins of a construction as bit strings of the polynomial's length, without reducing `coinLen` or
the construction. -/
def coinsEquivPoly {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) :
    A.Coins n ≃ (Fin (c.eval n) → Bool) :=
  Equiv.arrowCongr (finCongr (by rw [coinLen_eq, h])) (Equiv.refl Bool)

/-- The coin equivalence keeps the coin string:
`List.ofFn (coinsEquivPoly h n r) = List.ofFn r`. -/
theorem coinsEquivPoly_ofFn {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ) (r : A.Coins n) :
    List.ofFn (coinsEquivPoly h n r) = List.ofFn r :=
  (List.ofFn_congr (by rw [coinLen_eq, h]) r).symm

/-- The inverse coin equivalence keeps the coin string:
`List.ofFn ((coinsEquivPoly h n).symm w) = List.ofFn w`. -/
theorem coinsEquivPoly_symm_ofFn {A : NUPPT} {c : PolyExpr} (h : A.coins = c) (n : ℕ)
    (w : Fin (c.eval n) → Bool) : List.ofFn ((coinsEquivPoly h n).symm w) = List.ofFn w := by
  rw [← coinsEquivPoly_ofFn h n, Equiv.apply_symm_apply]

/-- The input-length-indexed activation `A_{|y|}(y)` of [PS10, Definition 26.8]: the
parameter is the input length (the `1^{|y|}` prefix carries no information). It is the layout
of the literal forms of [PS10, Definition 26.1] and [PS10, Definition 69.4] (D5). -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r

/-- The defining equation of `runLit`: `A.runLit y r = A.runAt |y| y r`. -/
theorem runLit_eq (y : List Bool) (r : A.Coins y.length) : A.runLit y r = A.runAt y.length y r :=
  rfl

/-- `A` is *uniform* — a PPT [PS10, Definition 23.4] — when its advice is empty at every
parameter. -/
def Uniform : Prop := ∀ n, A.advice n = []

/-- Uniformity is the conjunction of the advice clauses (definitional unfolding):
`A.Uniform ↔ ∀ n, A.advice n = []`. -/
theorem uniform_iff : A.Uniform ↔ ∀ n, A.advice n = [] := Iff.rfl

/-- A uniform machine has empty advice at every parameter. -/
theorem Uniform.advice_eq {A : NUPPT} (h : A.Uniform) (n : ℕ) : A.advice n = [] := h n

/-- `A` computes `f` with probability one [PS10, Definition 24.6]: at every parameter `n`,
on every argument `y` and for **every** coin string `r`, `A(1^n, y; r) = f(⟨1^n, y⟩)`. On
the finite uniform coin space "probability one" is the same as "every coin string"
(`TCSlib.Cryptography.Asymptotic.Adversary`, `NUPPT.computes_iff_uprob`).

The definition does not require `A.Uniform`. [PS10, Definition 24.6] is about a randomized
algorithm, i.e. a PPT, and is the case `A.Uniform ∧ A.Computes f`. For a non-uniform `A` this
is the advice analogue, which holds for uncomputable functions: with advice `[h n]` at
parameter `n` for an arbitrary `h : ℕ → Bool` (`ofPolyTime` of the advice projection), `A`
computes `w ↦ [h |fst w|]`. So `∃ A : NUPPT, A.Computes f` does **not** mean "a PPT computes
`f`"; where the text means efficient computation, the form is `A.Uniform ∧ A.Computes f`
(`exists_uniform_computes`; conversely `NUPPT.Computes.polyTimeComputable` of
`TCSlib.Complexity.Randomized.Closure`, which assumes `Uniform`).

`Computes f` constrains `f` only on the encodings `advInput n y = ⟨1^n, y⟩`: off them `f` is
arbitrary, even uncomputable, so `A.Uniform ∧ A.Computes f` is efficient computation of `f` on
those encodings, not of `f` on every string (the converse gives polynomial-time computability of
`z ↦ f ⟨1^{|fst z|}, snd z⟩`; gate 03a, round 2, R2-1). -/
def Computes (f : List Bool → List Bool) : Prop :=
  ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)

/-- The defining property of `Computes`: `A.Computes f ↔ ∀ n y r, A.runAt n y r = f ⟨1^n, y⟩`. -/
theorem computes_iff (f : List Bool → List Bool) :
    A.Computes f ↔ ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y) :=
  Iff.rfl

/-- A machine that computes `f` returns `f ⟨1^n, y⟩` on every activation. -/
theorem Computes.runAt_eq {f : List Bool → List Bool} (h : A.Computes f) (n : ℕ)
    (y : List Bool) (r : A.Coins n) : A.runAt n y r = f (advInput n y) :=
  h n y r

/-- The `NUPPT` whose machine is a polynomial-time machine for `f` (chosen from the
`PolyTimeComputable` witness), with the given coin polynomial and advice. Its output function
is `f` (`output_ofPolyTime`). This is how every reduction of the campaign is packaged: the
reduction is an FP function of the raw input `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` (D2). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool)
    (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT where
  M := Classical.choose ((polyTimeComputable_iff f).1 hf)
  Ct := Classical.choose (Classical.choose_spec ((polyTimeComputable_iff f).1 hf))
  ct := Classical.choose (Classical.choose_spec
      (Classical.choose_spec ((polyTimeComputable_iff f).1 hf)))
  coins := coins
  adv := adv
  advice := advice
  advice_length := hα
  halts := fun z => ⟨f z, (FinTM.computesFunInTime_iff _ _ _).1 (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec ((polyTimeComputable_iff f).1 hf)))) z⟩

/-- The output function of `ofPolyTime hf …` is `f` (determinism of completed outputs). -/
theorem output_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).output = f := by
  funext z
  exact (ofPolyTime hf coins adv advice hα).output_eq_of_computesInTime
    ((FinTM.computesFunInTime_iff _ _ _).1 (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec ((polyTimeComputable_iff f).1 hf)))) z)

/-- The coin polynomial of `ofPolyTime hf coins adv advice hα` is `coins`. -/
@[simp] theorem coins_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).coins = coins := rfl

/-- **The coins of `ofPolyTime hf coins …`** are `coins(n)` bits: the published equivalence
`(ofPolyTime hf coins adv advice hα).Coins n ≃ {0,1}^{coins(n)}` (`coinsEquivPoly`). -/
noncomputable def coinsEquiv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) : (ofPolyTime hf coins adv advice hα).Coins n ≃ (Fin (coins.eval n) → Bool) :=
  coinsEquivPoly (coins_ofPolyTime hf coins adv advice hα) n

/-- The coin equivalence of `ofPolyTime` keeps the coin string. -/
theorem coinsEquiv_ofPolyTime_ofFn {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) (r : (ofPolyTime hf coins adv advice hα).Coins n) :
    List.ofFn (coinsEquiv_ofPolyTime hf coins adv advice hα n r) = List.ofFn r :=
  coinsEquivPoly_ofFn _ n r

/-- The advice polynomial of `ofPolyTime hf coins adv advice hα` is `adv`. -/
@[simp] theorem adv_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).adv = adv := rfl

/-- The advice of `ofPolyTime hf coins adv advice hα` is `advice`. -/
@[simp] theorem advice_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :
    (ofPolyTime hf coins adv advice hα).advice = advice := rfl

/-- The untyped activation of `ofPolyTime hf …` is `f` on the raw layout. -/
theorem runAtL_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins adv : PolyExpr) (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n)
    (n : ℕ) (y r : List Bool) :
    (ofPolyTime hf coins adv advice hα).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) (advice n)) r) := by
  simp [runAtL, output_ofPolyTime]

/-- The uniform `NUPPT` with output function `f`: `ofPolyTime` with empty advice. -/
noncomputable def ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : NUPPT :=
  ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- `ofPolyTimeUniform hf coins` is uniform. -/
theorem ofPolyTimeUniform_uniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).Uniform := fun _ => rfl

/-- The output function of `ofPolyTimeUniform hf coins` is `f`. -/
theorem output_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).output = f :=
  output_ofPolyTime hf coins (.const 0) (fun _ => []) (fun _ => by simp)

/-- The coin polynomial of `ofPolyTimeUniform hf coins` is `coins`. -/
@[simp] theorem coins_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTimeUniform hf coins).coins = coins := rfl

/-- **The coins of `ofPolyTimeUniform hf coins`** are `coins(n)` bits: the published equivalence
`(ofPolyTimeUniform hf coins).Coins n ≃ {0,1}^{coins(n)}` (`coinsEquivPoly`). -/
noncomputable def coinsEquiv_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) : (ofPolyTimeUniform hf coins).Coins n ≃ (Fin (coins.eval n) → Bool) :=
  coinsEquivPoly (coins_ofPolyTimeUniform hf coins) n

/-- The coin equivalence of `ofPolyTimeUniform` keeps the coin string. -/
theorem coinsEquiv_ofPolyTimeUniform_ofFn {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) (r : (ofPolyTimeUniform hf coins).Coins n) :
    List.ofFn (coinsEquiv_ofPolyTimeUniform hf coins n r) = List.ofFn r :=
  coinsEquivPoly_ofFn _ n r

/-- The untyped activation of `ofPolyTimeUniform hf coins` is `f` on the raw layout with
empty advice. -/
theorem runAtL_ofPolyTimeUniform {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) (n : ℕ) (y r : List Bool) :
    (ofPolyTimeUniform hf coins).runAtL n y r =
      f (pairEncode (pairEncode (advInput n y) []) r) := by
  simp [runAtL, ofPolyTimeUniform, output_ofPolyTime]

/-- **Non-vacuity of [PS10, Definition 24.6].** Every polynomial-time computable function
`f` is computed with probability one by a PPT (a uniform `NUPPT`): the machine for
`f ∘ pairFstD ∘ pairFstD` applied to the raw input `⟨⟨⟨1^n, y⟩, []⟩, r⟩` ignores the advice
and the coins and returns `f ⟨1^n, y⟩`. (This is the direction "`PolyTimeComputable f` gives a
PPT computing `f`" of the equivalence behind Deviation 3, `FunFamily.Easy`.) -/
theorem exists_uniform_computes {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : ∃ A : NUPPT, A.Uniform ∧ A.coins = coins ∧ A.Computes f := by
  have hF : PolyTimeComputable fun z => f (pairFstD (pairFstD z)) :=
    hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  refine ⟨ofPolyTimeUniform hF coins, ofPolyTimeUniform_uniform hF coins, rfl, fun n y r => ?_⟩
  rw [runAt_eq, runAtL_ofPolyTimeUniform]
  simp

end NUPPT

/-- PPT [PS10, Definition 23.4] = non-uniform PPT with empty advice: the subtype of uniform
`NUPPT`s. -/
def PPT : Type 1 := {A : NUPPT // A.Uniform}

namespace PPT

/-- The underlying non-uniform machine of a PPT. -/
def toNUPPT (A : PPT) : NUPPT := A.1

/-- The underlying machine of the PPT built from a uniform `A`: `PPT.toNUPPT ⟨A, h⟩ = A`. -/
theorem toNUPPT_mk (A : NUPPT) (h : A.Uniform) : PPT.toNUPPT ⟨A, h⟩ = A := rfl

/-- A PPT has empty advice. -/
theorem uniform (A : PPT) : A.toNUPPT.Uniform := A.2

/-- The PPT with output function `f` and coin polynomial `coins`
(`Complexity.NUPPT.ofPolyTimeUniform`). -/
noncomputable def ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : PPT :=
  ⟨NUPPT.ofPolyTimeUniform hf coins, NUPPT.ofPolyTimeUniform_uniform hf coins⟩

/-- The underlying machine of `PPT.ofPolyTime hf coins` is `NUPPT.ofPolyTimeUniform hf coins`. -/
theorem toNUPPT_ofPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (coins : PolyExpr) : (ofPolyTime hf coins).toNUPPT = NUPPT.ofPolyTimeUniform hf coins := rfl

end PPT

/-- Non-vacuity: the class is inhabited (the identity machine with no coins). -/
theorem NUPPT.nonempty : Nonempty NUPPT :=
  ⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0)⟩

/-- Non-vacuity: the class of PPTs is inhabited. -/
theorem PPT.nonempty : Nonempty PPT :=
  ⟨⟨NUPPT.ofPolyTimeUniform polyTimeComputable_id (.const 0),
    NUPPT.ofPolyTimeUniform_uniform _ _⟩⟩

end Complexity
```


## ===== TCSlib/Complexity/Randomized/Closure.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The closure calculus of non-uniform PPTs

The class of non-uniform PPTs is closed under the operations every reduction of
[PS10, ch. 2–4] performs silently (inventory item Claim-26.3, "implicit throughout"):
pre- and post-composition with polynomial-time maps, parameter changes, hard-wiring advice,
using fresh coin segments as data, and sequential composition with fresh coins. Each lemma
here exhibits the composite machine as `Complexity.NUPPT.ofPolyTime` of an FP function of
the raw input `⟨⟨⟨1^n, y⟩, α⟩, r⟩` (foundation decision D2), built from
`NUPPT.polyTimeComputable_output`, the pairing calculus of
`TCSlib.Complexity.ClassNP.PolyTimePairing`, the unary evaluator
`Complexity.polyTimeComputable_unaryPoly` and the typed coin cuts
`polyTimeComputable_pairTakePoly`/`pairDropPoly` of
`TCSlib.Complexity.Randomized.Primitives`; the functional equation is
`NUPPT.runAtL_ofPolyTime` followed by the projection identities of the layout.
`Uniform` is preserved whenever the advice is the given machine's or empty.

The supplier table (DESIGN.md §2.5):

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_compParam` | `pre ⟨1^n, y⟩`, then `A.output`, then `post ⟨1^n, ·⟩` | projections, `comp` |
| `exists_comp` | `exists_compParam` with `pre`, `post` ignoring `1^n` | `exists_compParam` |
| `exists_reparam p` | advice `A.advice (p n)`; replace `1^n` by `1^{p n}` (`unaryPoly p`) | `unaryPoly` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩`; cut `A.coins (φ n)` coins | `pairTakePoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `p n`; pass the head as data | `pairTakePoly`, `pairDropPoly` |
| `exists_seq` | cut at `A.coins n`; run `A`, then `B` on `⟨y, a⟩`; advice `⟨α_A, α_B⟩` | both outputs, cuts, pairing |

Not in this file (they are FP-level facts the campaign uses directly): negation and
`[true]`-normalisation of verdicts (`Turing.FinTM.computesFunInTime_ifEq` through
`exists_comp`), branching (`Complexity.polyTimeComputable_ite`), length tests
(`polyTimeComputable_lenEq`/`_lenLe`), and the loop fuel of the repetition lemma
(`TCSlib.Complexity.Randomized.Repetition`).

## Main definitions

* `Complexity.NUPPT.layout`, `NUPPT.inParam`, `NUPPT.inArg`, `NUPPT.inAdvice`,
  `NUPPT.inCoins` — the raw input layout `⟨⟨⟨u, y⟩, α⟩, r⟩` and its four projections.
* `Complexity.NUPPT.combineAdvice` — two advice strings as one, keeping `[]` when both are
  empty (so that sequential composition preserves uniformity).

## Main results

* `Complexity.NUPPT.exists_compParam` — closure under polynomial-time pre- and post-processing
  that reads the parameter (`pre` sees `⟨1^n, y⟩`, `post` sees `⟨1^n, output⟩`).
* `Complexity.NUPPT.exists_comp` — its case that does not read the parameter (`pre` sees only
  `y`, `post` only the output).
* `Complexity.NUPPT.exists_reparam` — parameter change `n ↦ p(n)` (uniformity preserved).
* `Complexity.NUPPT.exists_reparam_advice` — parameter change along a polynomially bounded
  `φ : ℕ → ℕ`, hard-wiring `1^{φ n}` and the advice at `φ n`; extra coins unread.
* `Complexity.NUPPT.exists_withAdvice` — hard-wiring an extra polynomial-length advice.
* `Complexity.NUPPT.exists_split` — the first `p(n)` coins passed as data.
* `Complexity.NUPPT.exists_seq` — sequential composition with input pass-through and fresh
  coins (the "sunglass" composition of [Gar26]'s reductions, at the machine level).
* `Complexity.NUPPT.Computes.polyTimeComputable` — a PPT computing `f` with probability one
  gives `f ∘ advInput` as a polynomial-time function (coins hard-wired to `1^{coins n}`).
* `Complexity.NUPPT.polyTimeComputable_layout` and the projection lemmas — the FP calculus of
  the layout.
* `Complexity.PolyTimeComputable.comp'`, `Complexity.PolyTimeComputable.congr` — composition in
  applied form, and transfer of polynomial time along a pointwise equality.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.1, the closure properties of (non-uniform) p.p.t. machines used implicitly throughout.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete reductions these machines package).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.2, closure of FP under composition.)
-/

namespace Complexity

open Turing

/-! ### Composition in applied form and transfer along pointwise equality -/

/-- **Composition in applied form**: if `g` and `f` are polynomial-time, so is `x ↦ g (f x)`.
This is `PolyTimeComputable.comp` stated without `Function.comp`, so that unification never has
to unfold a composite against a lambda (such matches can unfold bundle string functions). -/
theorem PolyTimeComputable.comp' {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun x => g (f x) :=
  hg.comp hf

/-- **Polynomial time transfers along pointwise equality**: if `f` is polynomial-time and
`f x = g x` for every `x`, then `g` is polynomial-time (Mathlib's `Continuous.congr`
orientation). -/
theorem PolyTimeComputable.congr {f g : List Bool → List Bool} (h : PolyTimeComputable f)
    (e : ∀ x, f x = g x) : PolyTimeComputable g :=
  (funext e : f = g) ▸ h

namespace NUPPT

/-! ### The raw input layout and its projections -/

/-- The raw machine input `⟨⟨⟨u, y⟩, α⟩, r⟩`: unary parameter `u`, argument `y`, advice `α`,
coins `r` (`runAtL n y r` is `output (layout 1^n y (advice n) r)`). -/
def layout (u y α r : List Bool) : List Bool := pairEncode (pairEncode (pairEncode u y) α) r

/-- The unary-parameter slot of a raw input. -/
def inParam (z : List Bool) : List Bool := pairFstD (pairFstD (pairFstD z))

/-- The argument slot of a raw input. -/
def inArg (z : List Bool) : List Bool := pairSndD (pairFstD (pairFstD z))

/-- The advice slot of a raw input. -/
def inAdvice (z : List Bool) : List Bool := pairSndD (pairFstD z)

/-- The coin slot of a raw input. -/
def inCoins (z : List Bool) : List Bool := pairSndD z

/-- The defining equation of `layout`:
`layout u y α r = pairEncode (pairEncode (pairEncode u y) α) r`. -/
theorem layout_eq (u y α r : List Bool) :
    layout u y α r = pairEncode (pairEncode (pairEncode u y) α) r := rfl

/-- The defining equation of `inParam`: `inParam z = pairFstD (pairFstD (pairFstD z))`. -/
theorem inParam_eq (z : List Bool) : inParam z = pairFstD (pairFstD (pairFstD z)) := rfl

/-- The defining equation of `inArg`: `inArg z = pairSndD (pairFstD (pairFstD z))`. -/
theorem inArg_eq (z : List Bool) : inArg z = pairSndD (pairFstD (pairFstD z)) := rfl

/-- The defining equation of `inAdvice`: `inAdvice z = pairSndD (pairFstD z)`. -/
theorem inAdvice_eq (z : List Bool) : inAdvice z = pairSndD (pairFstD z) := rfl

/-- The defining equation of `inCoins`: `inCoins z = pairSndD z`. -/
theorem inCoins_eq (z : List Bool) : inCoins z = pairSndD z := rfl

/-- The parameter slot of a layout. -/
@[simp] theorem inParam_layout (u y α r : List Bool) : inParam (layout u y α r) = u := by
  simp [inParam, layout]

/-- The argument slot of a layout. -/
@[simp] theorem inArg_layout (u y α r : List Bool) : inArg (layout u y α r) = y := by
  simp [inArg, layout]

/-- The advice slot of a layout. -/
@[simp] theorem inAdvice_layout (u y α r : List Bool) : inAdvice (layout u y α r) = α := by
  simp [inAdvice, layout]

/-- The coin slot of a layout. -/
@[simp] theorem inCoins_layout (u y α r : List Bool) : inCoins (layout u y α r) = r := by
  simp [inCoins, layout]

/-- An activation is the output on the layout `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. -/
theorem runAtL_eq_output_layout (A : NUPPT) (n : ℕ) (y r : List Bool) :
    A.runAtL n y r = A.output (layout (List.replicate n true) y (A.advice n) r) := by
  rw [runAtL_eq, advInput_eq]
  rfl

/-- The parameter projection is polynomial-time. -/
theorem polyTimeComputable_inParam : PolyTimeComputable inParam :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)

/-- The argument projection is polynomial-time. -/
theorem polyTimeComputable_inArg : PolyTimeComputable inArg :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)

/-- The advice projection is polynomial-time. -/
theorem polyTimeComputable_inAdvice : PolyTimeComputable inAdvice :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The coin projection is polynomial-time. -/
theorem polyTimeComputable_inCoins : PolyTimeComputable inCoins :=
  polyTimeComputable_pairSndD

/-- Assembling a layout from four polynomial-time functions is polynomial-time
(three applications of `PolyTimeComputable.pairEncode`). -/
theorem polyTimeComputable_layout {f₁ f₂ f₃ f₄ : List Bool → List Bool}
    (h₁ : PolyTimeComputable f₁) (h₂ : PolyTimeComputable f₂) (h₃ : PolyTimeComputable f₃)
    (h₄ : PolyTimeComputable f₄) :
    PolyTimeComputable fun z => layout (f₁ z) (f₂ z) (f₃ z) (f₄ z) :=
  ((h₁.pairEncode h₂).pairEncode h₃).pairEncode h₄

/-! ### Combined advice -/

/-- Two advice strings as one: `⟨a, b⟩`, except that two empty strings combine to `[]`
(so that composing uniform machines gives a uniform machine). Decoded by `pairFstD` and
`pairSndD`, which return `[]` on `[]`. -/
def combineAdvice (a b : List Bool) : List Bool :=
  if a = [] ∧ b = [] then [] else pairEncode a b

/-- Decoding the first combined advice string. -/
@[simp] theorem pairFstD_combineAdvice (a b : List Bool) : pairFstD (combineAdvice a b) = a := by
  unfold combineAdvice
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact pairFstD_of_pairDecode_eq_none Turing.pairDecode_nil
  · simp

/-- Decoding the second combined advice string. -/
@[simp] theorem pairSndD_combineAdvice (a b : List Bool) : pairSndD (combineAdvice a b) = b := by
  unfold combineAdvice
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil
  · simp

/-- Two empty advice strings combine to the empty string. -/
theorem combineAdvice_nil : combineAdvice [] [] = [] := by
  simp [combineAdvice]

/-- The combined advice has length at most `2|a| + 2 + |b|`. -/
theorem length_combineAdvice_le (a b : List Bool) :
    (combineAdvice a b).length ≤ 2 * a.length + 2 + b.length := by
  unfold combineAdvice
  split_ifs
  · simp
  · rw [length_pairEncode]

/-! ### The closure catalogue -/

/-- **Closure under parameter-aware pre- and post-processing** [PS10, §2.1, implicit;
inventory Claim-26.3(a), (b)] (gate 03a, finding 3): for an `NUPPT` `A` and polynomial-time
`pre`, `post` there is an `NUPPT` `B` with the same coins and advice that, at parameter `n` on
argument `y` with coins `r`, computes `post ⟨1^n, A(1^n, pre ⟨1^n, y⟩; r)⟩`: `pre` sees the
adversary input `⟨1^n, y⟩` (`advInput n y`), and `post` sees the parameter `1^n` paired with
`A`'s output. `exists_comp` is the case where `pre` and `post` ignore `1^n`.

**Proof sketch.** The raw function is
`z ↦ post ⟨inParam z, A.output (layout (inParam z) (pre ⟨inParam z, inArg z⟩) (inAdvice z)
(inCoins z))⟩`, polynomial-time by `polyTimeComputable_layout`,
`PolyTimeComputable.pairEncode`, `PolyTimeComputable.comp`, `NUPPT.polyTimeComputable_output`,
`hpre`, `hpost`; `B := ofPolyTime` of it with `A`'s coins and advice. On the layout
`⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` the projections return the slots (`runAtL_ofPolyTime`, the
`pairFstD_pairEncode`/`pairSndD_pairEncode` identities), so `⟨inParam z, inArg z⟩` is
`⟨1^n, y⟩ = advInput n y` and the value is `post ⟨1^n, A.runAtL n (pre (advInput n y)) r⟩`. -/
theorem exists_compParam (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r =
        post (pairEncode (List.replicate n true) (A.runAtL n (pre (advInput n y)) r)) := by
  have hF := PolyTimeComputable.comp' hpost (polyTimeComputable_inParam.pairEncode
    (PolyTimeComputable.comp' A.polyTimeComputable_output
        (polyTimeComputable_layout polyTimeComputable_inParam
      (PolyTimeComputable.comp' hpre
          (polyTimeComputable_inParam.pairEncode polyTimeComputable_inArg))
      polyTimeComputable_inAdvice polyTimeComputable_inCoins)))
  refine ⟨ofPolyTime hF A.coins A.adv A.advice A.advice_length, coins_ofPolyTime _ _ _ _ _,
    adv_ofPolyTime _ _ _ _ _, advice_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL_eq, advInput_eq, layout, inParam, inArg, inAdvice, inCoins]

/-- **Closure under polynomial-time pre- and post-processing** [PS10, §2.1, implicit;
inventory Claim-26.3(a), (b)]: for an `NUPPT` `A` and polynomial-time `pre`, `post` there is an
`NUPPT` `B` with the same coins and advice that computes `post (A(1^n, pre y; r))`.

**Scope** (gate 03a, finding 3): `pre` sees only the argument `y` and `post` only `A`'s output;
neither sees `1^n`. Pre- and post-processing that depends on the parameter (padding or cutting
to `ℓ'(n)` bits, slicing `p(n)` bits, planting at a position that depends on `n`) is the
parameter-aware form `exists_compParam`, where `pre` sees `⟨1^n, y⟩` and `post` sees `1^n`
paired with the output. Reductions that also read the advice or the coins are built as
`ofPolyTime` of a raw function of the layout (`inParam`, `inArg`, `inAdvice`, `inCoins`,
`polyTimeComputable_layout`), as `EnsembleLemmas.exists_pushRed` does for [PS10, Lemma 71.5].

**Proof sketch.** `exists_compParam` with `pre ∘ snd` and `post ∘ snd`: the second component of
`advInput n y = ⟨1^n, y⟩` is `y`, and that of `⟨1^n, A.runAtL n (pre y) r⟩` is `A`'s output
(`pairSndD_pairEncode`). -/
theorem exists_comp (A : NUPPT) {pre post : List Bool → List Bool}
    (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r) := by
  obtain ⟨B, hc, ha, hα, hB⟩ := exists_compParam A (PolyTimeComputable.comp' hpre polyTimeComputable_pairSndD)
    (PolyTimeComputable.comp' hpost polyTimeComputable_pairSndD)
  refine ⟨B, hc, ha, hα, fun n y r => ?_⟩
  rw [hB, pairSndD_pairEncode]
  simp [advInput_eq]

/-- **Parameter change `n ↦ p(n)`** [PS10, §2.1, implicit; inventory Claim-26.3]: for an
`NUPPT` `A` and a syntactic polynomial `p` there is an `NUPPT` `B` with coins `A.coins.subst p`
that at parameter `n` behaves as `A` at parameter `p(n)`; `B` is uniform when `A` is (the
prefix `1^{p(n)}` is computed, not hard-wired).

**Proof sketch.** Advice `A.advice (p n)` of length `≤ (A.adv.subst p).eval n`
(`PolyExpr.eval_subst`); the raw function replaces the parameter slot `1^n` by
`1^{p(|1^n|)} = 1^{p n}` (`polyTimeComputable_unaryPoly p` on `inParam`) and re-pairs
(`polyTimeComputable_layout`), then applies `A.output`; the equation is `runAtL_ofPolyTime`
plus the projection identities and `List.length_replicate`. -/
theorem exists_reparam (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r := by
  have hF := PolyTimeComputable.comp' A.polyTimeComputable_output
    (polyTimeComputable_layout
      (PolyTimeComputable.comp' (polyTimeComputable_unaryPoly p) polyTimeComputable_inParam)
      polyTimeComputable_inArg polyTimeComputable_inAdvice polyTimeComputable_inCoins)
  have hadv : ∀ n, (A.advice (p.eval n)).length ≤ (A.adv.subst p).eval n := fun n => by
    rw [PolyExpr.eval_subst]
    exact A.advice_length _
  refine ⟨ofPolyTime hF (A.coins.subst p) (A.adv.subst p) (fun n => A.advice (p.eval n)) hadv,
    coins_ofPolyTime _ _ _ _ _, fun hA => (uniform_iff _).2 fun n =>
      (congrFun (advice_ofPolyTime _ _ _ _ _) n).trans ((uniform_iff A).1 hA _), fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL_eq, advInput_eq, layout, inParam, inArg, inAdvice, inCoins]

/-- **Parameter change along an arbitrary polynomially bounded `φ : ℕ → ℕ`** (non-uniform)
[PS10, §2.1, implicit; inventory Claim-26.3(d)]: for an `NUPPT` `A`, `φ` with `φ n ≤ p n`,
there is an `NUPPT` `B` with coins `A.coins.subst p` that at parameter `n` behaves as `A` at
parameter `φ n` on the first `A.coins (φ n)` coins (extra coins are unread). This is the one
place an abstract `ℕ → ℕ` appears (as a hypothesis with a `PolyExpr` majorant, D9); it serves
Lemma 64.3's `m(n) = n − ⌊log₂ n⌋`, the literal/`1^n` bridges of Definitions 26.1 and 69.4, and
the interdefinability argument of D3/D4.

**Proof sketch.** Advice `⟨1^{φ n}, A.advice (φ n)⟩`, of length
`2 φ n + 2 + |A.advice (φ n)| ≤ 2 p n + 2 + A.adv (p n)` by `hφ`, `advice_length` and
`PolyExpr.eval_mono` — the bound `add (add (mul (const 2) p) (const 2)) (A.adv.subst p)`. The
raw function reads `w := 1^{φ n}` and `α := A.advice (φ n)` from the advice slot
(`pairFstD`/`pairSndD` of `inAdvice`), cuts the coins to `A.coins.eval |w|` bits
(`polyTimeComputable_pairTakePoly A.coins` on `⟨w, inCoins z⟩`), and runs `A.output` on
`layout w (inArg z) α coins'`; `B.coins = A.coins.subst p ≥ A.coins (φ n)` by `eval_mono`, so
the cut reads existing coins. The equation is `runAtL_ofPolyTime` plus the projection
identities. -/
theorem exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr)
    (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n))) := by
  have hw := PolyTimeComputable.comp' polyTimeComputable_pairFstD polyTimeComputable_inAdvice
  have hF := PolyTimeComputable.comp' A.polyTimeComputable_output
    (polyTimeComputable_layout hw polyTimeComputable_inArg
      (PolyTimeComputable.comp' polyTimeComputable_pairSndD polyTimeComputable_inAdvice)
      (PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly A.coins)
          (hw.pairEncode polyTimeComputable_inCoins)))
  have hadv : ∀ n, (pairEncode (List.replicate (φ n) true) (A.advice (φ n))).length ≤
      (PolyExpr.add (.add (.mul (.const 2) p) (.const 2)) (A.adv.subst p)).eval n := fun n => by
    rw [length_pairEncode, List.length_replicate]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_subst]
    have h₁ := hφ n
    have h₂ := A.advice_length (φ n)
    have h₃ := A.adv.eval_mono (hφ n)
    omega
  refine ⟨ofPolyTime hF (A.coins.subst p) _
    (fun n => pairEncode (List.replicate (φ n) true) (A.advice (φ n))) hadv,
    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL_eq, advInput_eq, coinLen_eq, layout, inArg, inAdvice, inCoins]

/-- **Hard-wiring advice** [PS10, §2.1, implicit; inventory Claim-26.3(d)]: for an `NUPPT` `A`
and a polynomially bounded family `β n` there is an `NUPPT` `B` with the same coins that
computes `A(1^n, ⟨y, β n⟩; r)` (the reductions of chapters 2–4 hard-wire hybrid indices,
worst-case inputs and the given adversary's advice this way).

**Proof sketch.** Advice `⟨A.advice n, β n⟩` of length `2 A.adv n + 2 + b n`
(`length_pairEncode`); the raw function re-pairs the argument slot with the second half of
the advice slot and runs `A.output` with the first half as advice
(`polyTimeComputable_layout`, projections). -/
theorem exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr)
    (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r := by
  have hF := PolyTimeComputable.comp' A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam
      (polyTimeComputable_inArg.pairEncode
        (PolyTimeComputable.comp' polyTimeComputable_pairSndD polyTimeComputable_inAdvice))
      (PolyTimeComputable.comp' polyTimeComputable_pairFstD
          polyTimeComputable_inAdvice) polyTimeComputable_inCoins)
  have hadv : ∀ n, (pairEncode (A.advice n) (β n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) b).eval n := fun n => by
    rw [length_pairEncode]
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    have h₁ := A.advice_length n
    have h₂ := hβ n
    omega
  refine ⟨ofPolyTime hF A.coins _ (fun n => pairEncode (A.advice n) (β n)) hadv,
    coins_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL_eq, advInput_eq, layout, inParam, inArg, inAdvice, inCoins]

/-- **Extra coins passed as data** [PS10, §2.1, implicit; inventory Claim-26.3(c)]: for an
`NUPPT` `A` and a syntactic polynomial `p` there is an `NUPPT` `B` with coins `p + A.coins`
and `A`'s advice such that `B(1^n, y; r) = A(1^n, ⟨y, r.take (p n)⟩; r.drop (p n))`: the first
`p n` coins become part of the input (a uniformly random string of length `p n`), the rest are
`A`'s coins.

**Proof sketch.** The raw function cuts the coin slot at `p(|1^n|)` with
`polyTimeComputable_pairTakePoly p`/`pairDropPoly p` on `⟨inParam z, inCoins z⟩`, re-pairs the
argument with the head and runs `A.output` with the tail as coins; the equation is
`runAtL_ofPolyTime`, the projection identities and `List.length_replicate`. -/
theorem exists_split (A : NUPPT) (p : PolyExpr) :
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r =
        A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hF := PolyTimeComputable.comp' A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam
      (polyTimeComputable_inArg.pairEncode
          (PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly p) hcut))
      polyTimeComputable_inAdvice (PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly p)
          hcut))
  refine ⟨ofPolyTime hF (.add p A.coins) A.adv A.advice A.advice_length,
    coins_ofPolyTime _ _ _ _ _, advice_ofPolyTime _ _ _ _ _, fun n y r => ?_⟩
  rw [runAtL_ofPolyTime]
  simp [runAtL_eq, advInput_eq, layout, inParam, inArg, inAdvice, inCoins]

/-- **Sequential composition with input pass-through and fresh coins** [PS10, §2.1, implicit;
inventory Claim-26.3(b), (c), (e) with one call]: for `NUPPT`s `A`, `B` there is an `NUPPT`
`C` with coins `A.coins + B.coins`, uniform when both are, computing
`B(1^n, ⟨y, A(1^n, y; r₁)⟩; r₂)` where `r = r₁ ++ r₂` is cut at `A.coins n`. This is the
machine-level form of the "sunglass" reduction `D' := D ∘ (sampler)` of [Gar26] used by
Lemma 71.5 (`Indist.push`) and every two-stage reduction.

**Proof sketch.** Advice `combineAdvice (A.advice n) (B.advice n)` of length
`≤ 2 A.adv n + 2 + B.adv n` (`length_combineAdvice_le`), equal to `[]` when both are empty
(`combineAdvice_nil`, so uniformity is preserved). The raw function cuts the coins at
`A.coins(|1^n|)` (`pairTakePoly`/`pairDropPoly` on `⟨inParam z, inCoins z⟩`), runs `A.output` on
`layout (inParam z) (inArg z) (pairFstD (inAdvice z)) r₁`, pairs the result with the argument
and runs `B.output` on `layout (inParam z) ⟨inArg z, a⟩ (pairSndD (inAdvice z)) r₂`; the
equation is `runAtL_ofPolyTime`, the projection identities, `pairFstD_combineAdvice`,
`pairSndD_combineAdvice` and `List.length_replicate`. -/
theorem exists_seq (A B : NUPPT) :
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n)) := by
  have hcut := polyTimeComputable_inParam.pairEncode polyTimeComputable_inCoins
  have hr₁ := PolyTimeComputable.comp' (polyTimeComputable_pairTakePoly A.coins) hcut
  have hr₂ := PolyTimeComputable.comp' (polyTimeComputable_pairDropPoly A.coins) hcut
  have ha := PolyTimeComputable.comp' A.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam polyTimeComputable_inArg
      (PolyTimeComputable.comp' polyTimeComputable_pairFstD polyTimeComputable_inAdvice) hr₁)
  have hF := PolyTimeComputable.comp' B.polyTimeComputable_output
    (polyTimeComputable_layout polyTimeComputable_inParam (polyTimeComputable_inArg.pairEncode ha)
      (PolyTimeComputable.comp' polyTimeComputable_pairSndD polyTimeComputable_inAdvice) hr₂)
  have hadv : ∀ n, (combineAdvice (A.advice n) (B.advice n)).length ≤
      (PolyExpr.add (.add (.mul (.const 2) A.adv) (.const 2)) B.adv).eval n := fun n => by
    have h₁ := length_combineAdvice_le (A.advice n) (B.advice n)
    have h₂ := A.advice_length n
    have h₃ := B.advice_length n
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  refine ⟨ofPolyTime hF (.add A.coins B.coins) _
    (fun n => combineAdvice (A.advice n) (B.advice n)) hadv, coins_ofPolyTime _ _ _ _ _,
    fun hA hB => (uniform_iff _).2 fun n => ?_, fun n y r => ?_⟩
  · rw [advice_ofPolyTime, (uniform_iff A).1 hA n, (uniform_iff B).1 hB n, combineAdvice_nil]
  · rw [runAtL_ofPolyTime]
    simp [runAtL_eq, advInput_eq, coinLen_eq, layout, inParam, inArg, inAdvice, inCoins]

/-- **From "computes with probability one" to FP** [PS10, Definition 24.6; the direction
"a PPT computing `f` gives a polynomial-time evaluator" behind Deviation 3]: if a uniform
`A` computes `f`, then `z ↦ f ⟨1^{|fst z|}, snd z⟩` is polynomial-time computable — run `A`
with the coins hard-wired to the all-`true` string of length `coins n`.

**Proof sketch.** The raw function `z ↦ A.output (layout 1^{|fst z|} (snd z) [] 1^{A.coins |fst z|})`
is polynomial-time (`polyTimeComputable_unary`, `polyTimeComputable_unaryPoly A.coins`,
`polyTimeComputable_layout`); by `Computes` at parameter `|fst z|`, argument `snd z` and
the constant coin string `fun _ => true` (`List.ofFn_const`), it equals
`f (advInput |fst z| (snd z))` everywhere. -/
theorem Computes.polyTimeComputable {A : NUPPT} {f : List Bool → List Bool} (hA : A.Uniform)
    (h : A.Computes f) :
    PolyTimeComputable fun z => f (advInput (pairFstD z).length (pairSndD z)) := by
  have hF := PolyTimeComputable.comp' A.polyTimeComputable_output
    (polyTimeComputable_layout
        (PolyTimeComputable.comp' polyTimeComputable_unary polyTimeComputable_pairFstD)
      polyTimeComputable_pairSndD (polyTimeComputable_const [])
      (PolyTimeComputable.comp' (polyTimeComputable_unaryPoly A.coins) polyTimeComputable_pairFstD))
  convert hF using 1
  funext z
  have hz := Computes.runAt_eq A h (pairFstD z).length (pairSndD z) (fun _ => true)
  have hadv := (uniform_iff A).1 hA (pairFstD z).length
  simp only [NUPPT.runAt_eq, NUPPT.runAtL_eq, List.ofFn_const] at hz
  rw [← hz]
  simp [layout, advInput_eq, coinLen_eq, hadv]

end NUPPT

end Complexity
```


## ===== TCSlib/Complexity/ClassP/BinaryArith/Loops.lean =====

```text
/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import TCSlib.Complexity.ClassP.BinaryArith.Iterate
import TCSlib.Complexity.ClassP.BinaryArith.AddSub
import TCSlib.Complexity.ClassP.BinaryArith.Mul
import TCSlib.Complexity.ClassP.BinaryArith.Div
import TCSlib.Complexity.ClassP.BinaryArith.Words
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.CircuitComplexity.UnaryCode
import TCSlib.Complexity.ClassNP.PolyTimePrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counted loops, unary numbers and word tools in polynomial time

Generic polynomial-time word functions on `Turing.pairEncode`-structured inputs, shared by
the randomized algorithms of [AB09, §7.2.3–7.2.4]: a counted loop (a host: run a step once
per letter of a unary counter), the reading of unary numbers, the lookup of an entry in an
encoded list of words (`Complexity.BinArith.encWords`), word equality, unary multiplication,
and the cutting of a word into blocks. Not themselves results of the book.

## Main definitions

* `Complexity.BinArith.forLoop` — run a step once per letter of a unary counter.
* `Complexity.BinArith.uHead`, `Complexity.BinArith.uRest`, `Complexity.BinArith.hasFalse` —
  the leading `1`s of a word, the rest after the first `0`, and whether there is a `0`.
* `Complexity.BinArith.getW` — the `j`-th entry of an encoded list of words.
* `Complexity.BinArith.eqW` — equality of the two components of a pair.
* `Complexity.BinArith.mulU` — unary multiplication (`|a|` copies of `b` on `⟨a, b⟩`).
* `Complexity.BinArith.chunkW`, `Complexity.BinArith.chunkList` — cutting a word into blocks
  of `|c|` bits, as a list of words.

## Main results

* `Complexity.BinArith.forLoop_pairEncode`, `Complexity.BinArith.polyTimeComputable_forLoop`,
  `Complexity.BinArith.forLoop_bound_of_ctx` — the counted loop and its time bound.
* `Complexity.BinArith.decodeNat_eq` — `BoolCircuit.decodeNat` through `uHead` and `uRest`.
* `Complexity.BinArith.getW_pairEncode`, `Complexity.BinArith.polyTimeComputable_getW`.
* `Complexity.BinArith.eqW_pairEncode`, `Complexity.BinArith.length_mulU`,
  `Complexity.BinArith.chunkW_pairEncode` — what they compute, and their
  `polyTimeComputable_*` lemmas.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Complexity

namespace BinArith

open Turing
open Complexity.LogProg (bitsVal eq_of_bitsVal_eq)

/-- Composition in applied form: `x ↦ f (g x)` is polynomial-time when `f` and `g` are.  (Stated
with an applied body so that unification never unfolds `f`.) -/
theorem polyTimeComputable_app {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable (fun x => f (g x)) :=
  hf.comp hg

/-- A one-bit test of a polynomial-time function, in applied form. -/
theorem polyTimeComputable_test_app {p : List Bool → Bool} {g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => [p (g x)]) :=
  hp.comp hg

/-! ### The counted loop -/

/-- One round of the counted loop on `⟨c, d⟩`: if `c ≠ []`, drop a letter of `c` and apply
`f` to `d`; a state with empty (or malformed) counter is fixed. -/
def forStep (f : List Bool → List Bool) (S : List Bool) : List Bool :=
  if isNilB (pairFstD S) then S else pairEncode ((pairFstD S).drop 1) (f (pairSndD S))

/-- The counted loop: `|S| + 1` rounds of `forStep f` from `S`. -/
def forLoop (f : List Bool → List Bool) (S : List Bool) : List Bool :=
  (forStep f)^[1 * (S.length + 1) ^ 1] S

/-- The rounds of the counted loop from `⟨c, d⟩`. -/
theorem iterate_forStep (f : List Bool → List Bool) (c d : List Bool) (i : ℕ) :
    (forStep f)^[i] (pairEncode c d) = pairEncode (c.drop i) (f^[min i c.length] d) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : c.length ≤ i
    · have h1 : min i c.length = c.length := by omega
      have h2 : min (i + 1) c.length = c.length := by omega
      simp [forStep, isNilB_def, List.drop_eq_nil_of_le hi, List.drop_eq_nil_of_le (by omega :
        c.length ≤ i + 1), h1, h2]
    · have hne : c.drop i ≠ [] := by simp; omega
      have h1 : min i c.length = i := by omega
      have h2 : min (i + 1) c.length = i + 1 := by omega
      simp only [forStep, pairFstD_pairEncode, pairSndD_pairEncode, isNilB_def, hne,
        decide_false, Bool.false_eq_true, if_false, List.drop_drop, h1, h2,
        Function.iterate_succ_apply']

/-- **The counted loop runs `f` once per letter of the counter**:
`forLoop f ⟨c, d⟩ = ⟨[], f^[|c|] d⟩`. -/
theorem forLoop_pairEncode (f : List Bool → List Bool) (c d : List Bool) :
    forLoop f (pairEncode c d) = pairEncode [] (f^[c.length] d) := by
  unfold forLoop
  rw [iterate_forStep, List.drop_eq_nil_of_le (by simp [length_pairEncode]; omega)]
  congr 2
  simp [length_pairEncode]
  omega

/-- A state whose counter is empty is fixed by the round. -/
theorem forStep_of_fst_nil (f : List Bool → List Bool) {S : List Bool} (h : pairFstD S = []) :
    forStep f S = S := by
  simp [forStep, isNilB_def, h]

/-- **The counted loop is polynomial-time** when its body is and the iterates `f^[j] d`,
`j ≤ |c|`, stay inside a polynomial envelope of `|⟨c, d⟩|`.

**Proof sketch.** `forLoop f` is `polyTimeComputable_iterate` of the round `forStep f` (an
`ite` of polynomial-time pieces) from the input. A word that is not a pair has empty counter
and is fixed; on `⟨c, d⟩` the `i`-th iterate is `⟨c.drop i, f^[min i |c|] d⟩`
(`iterate_forStep`), whose length the envelope bounds. -/
theorem polyTimeComputable_forLoop {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (B b : ℕ) (hbound : ∀ c d j, j ≤ c.length →
      (f^[j] d).length ≤ B * ((pairEncode c d).length + 1) ^ b) :
    PolyTimeComputable (forLoop f) := by
  have hstep : PolyTimeComputable (forStep f) := by
    unfold forStep
    exact polyTimeComputable_ite (by
        simpa only [Function.comp_def, isNilB_def] using
          polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      polyTimeComputable_id
      ((polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
        (hf.comp polyTimeComputable_pairSndD))
  refine polyTimeComputable_iterate hstep polyTimeComputable_id 1 1 (B + 2) (b + 1)
    (fun S i _ => ?_)
  simp only [id_eq]
  have hP : 1 ≤ (S.length + 1) ^ b := Nat.one_le_pow _ _ (by omega)
  have hpow : (S.length + 1) ^ (b + 1) = (S.length + 1) ^ b * (S.length + 1) := pow_succ _ _
  have h5 : S.length + 1 ≤ (S.length + 1) ^ b * (S.length + 1) := Nat.le_mul_of_pos_left _ hP
  rw [hpow]
  cases hd : pairDecode S with
  | none =>
    have h0 : pairFstD S = [] := by simp [pairFstD_eq, hd]
    rw [Function.iterate_fixed (forStep_of_fst_nil f h0)]
    nlinarith
  | some cd =>
    obtain ⟨c, d⟩ := cd
    have hS := eq_pairEncode_of_pairDecode S c d hd
    have h1 := hbound c d (min i c.length) (by omega)
    rw [← hS] at h1
    rw [hS, iterate_forStep, length_pairEncode]
    rw [← hS]
    have h2 : (c.drop i).length ≤ c.length := by simp
    have h3 : 2 * c.length + 2 ≤ S.length := by rw [hS]; simp [length_pairEncode]
    have h6 : B * (S.length + 1) ^ b ≤ B * ((S.length + 1) ^ b * (S.length + 1)) :=
      Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
    nlinarith

/-- An iterate bound for context-preserving bodies: if `f ⟨q, ·⟩` keeps `q` and grows the
word by at most `A(|q| + 1)`, then `|f^[j] d| ≤ |d| + jA(|q| + 1)`. -/
theorem length_iterate_le_of_ctx {f : List Bool → List Bool} (A : ℕ)
    (hctx : ∀ d, pairFstD (f d) = pairFstD d)
    (hlen : ∀ d, (f d).length ≤ d.length + A * ((pairFstD d).length + 1)) (d : List Bool) (j : ℕ) :
    (f^[j] d).length ≤ d.length + j * (A * ((pairFstD d).length + 1)) := by
  have hq : ∀ j, pairFstD (f^[j] d) = pairFstD d := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hctx, ih]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    have := hlen (f^[j] d)
    rw [hq j] at this
    rw [Nat.succ_mul]
    omega

/-- The envelope required by `polyTimeComputable_forLoop`, for context-preserving bodies of
bounded growth. -/
theorem forLoop_bound_of_ctx {f : List Bool → List Bool} (A : ℕ)
    (hctx : ∀ d, pairFstD (f d) = pairFstD d)
    (hlen : ∀ d, (f d).length ≤ d.length + A * ((pairFstD d).length + 1)) :
    ∀ c d j, j ≤ c.length → (f^[j] d).length ≤ (A + 1) * ((pairEncode c d).length + 1) ^ 2 := by
  intro c d j hj
  have h := length_iterate_le_of_ctx A hctx hlen d j
  have hq := length_pairFstD_le d
  have hN : c.length + d.length ≤ (pairEncode c d).length := by simp [length_pairEncode]; omega
  set N := (pairEncode c d).length
  have h1 : j * (A * ((pairFstD d).length + 1)) ≤ N * (A * (N + 1)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul_left _ (by omega))
  nlinarith

/-! ### Unary numbers -/

/-- The transition of `uHead`: stay live while reading `1`s. -/
private def headδ (q b : Bool) : Bool := q && b

/-- The emission of `uHead`: copy the `1`s of the live phase. -/
private def headO (q b : Bool) : Option Bool := if q && b then some true else none

/-- The leading `1`s of a word (`1ʲ` on `1ʲ0w`). -/
def uHead (w : List Bool) : List Bool := transduce headδ headO true w

/-- The transition of `uRest`: switch on at the first `0`. -/
private def restδ (q b : Bool) : Bool := q || !b

/-- The emission of `uRest`: copy everything after the first `0`. -/
private def restO (q b : Bool) : Option Bool := if q then some b else none

/-- The word after the first `0` (`w` on `1ʲ0w`; `[]` if there is no `0`). -/
def uRest (w : List Bool) : List Bool := transduce restδ restO false w

/-- Whether a word contains a `0`. -/
def hasFalse (w : List Bool) : Bool := (w.map not).any id

/-- `hasFalse w` tests whether the list of negated bits contains `true`. -/
theorem hasFalse_eq (w : List Bool) : hasFalse w = (w.map not).any id := rfl

/-- The `uHead` transducer emits nothing once off. -/
private theorem transduce_head_false (w : List Bool) : transduce headδ headO false w = [] := by
  induction w with
  | nil => exact transduce_nil _ _ _
  | cons b w ih => simp [transduce_nil, transduce_cons, headδ, headO, ih]

/-- The `uRest` transducer copies everything once on. -/
private theorem transduce_rest_true (w : List Bool) : transduce restδ restO true w = w := by
  induction w with
  | nil => exact transduce_nil _ _ _
  | cons b w ih => simp [transduce_nil, transduce_cons, restδ, restO, ih]

/-- `uHead` on `0w` is empty. -/
@[simp] theorem uHead_false_cons (w : List Bool) : uHead (false :: w) = [] := by
  simp [uHead, transduce_nil, transduce_cons, headδ, headO, transduce_head_false]

/-- `uHead` on `1w`. -/
@[simp] theorem uHead_true_cons (w : List Bool) : uHead (true :: w) = true :: uHead w := by
  simp [uHead, transduce_nil, transduce_cons, headδ, headO]

/-- `uRest` on `0w` is `w`. -/
@[simp] theorem uRest_false_cons (w : List Bool) : uRest (false :: w) = w := by
  simp [uRest, transduce_nil, transduce_cons, restδ, restO, transduce_rest_true]

/-- `uRest` on `1w`. -/
@[simp] theorem uRest_true_cons (w : List Bool) : uRest (true :: w) = uRest w := by
  simp [uRest, transduce_nil, transduce_cons, restδ, restO]

/-- `uHead []` is empty. -/
@[simp] theorem uHead_nil : uHead [] = [] := transduce_nil _ _ _

/-- `uRest []` is empty. -/
@[simp] theorem uRest_nil : uRest [] = [] := transduce_nil _ _ _

/-- `hasFalse` on a cons. -/
@[simp] theorem hasFalse_cons (b : Bool) (w : List Bool) :
    hasFalse (b :: w) = (!b || hasFalse w) := by
  simp [hasFalse]

/-- `[]` has no `0`. -/
@[simp] theorem hasFalse_nil : hasFalse [] = false := rfl

/-- **Reading a unary number**: `decodeNat w` is `(|uHead w|, uRest w)` if `w` has a `0`. -/
theorem decodeNat_eq (w : List Bool) :
    BoolCircuit.decodeNat w =
      if hasFalse w then some ((uHead w).length, uRest w) else none := by
  induction w with
  | nil => rw [BoolCircuit.decodeNat_nil]; rfl
  | cons b w ih =>
    cases b
    · simp [BoolCircuit.decodeNat_nil, BoolCircuit.decodeNat_false_cons,
        BoolCircuit.decodeNat_true_cons]
    · simp only [BoolCircuit.decodeNat_nil, BoolCircuit.decodeNat_false_cons,
        BoolCircuit.decodeNat_true_cons, ih, uHead_true_cons, uRest_true_cons, hasFalse_cons,
        Bool.not_true, Bool.false_or, List.length_cons]
      split <;> simp

/-- Reading `1ʲ0w`. -/
theorem uHead_encodeNat (j : ℕ) (w : List Bool) :
    uHead (BoolCircuit.encodeNat j ++ w) = List.replicate j true := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat_def]
  | succ j ih => simpa [BoolCircuit.encodeNat_def, List.replicate_succ] using ih

/-- The rest of `1ʲ0w` is `w`. -/
theorem uRest_encodeNat (j : ℕ) (w : List Bool) :
    uRest (BoolCircuit.encodeNat j ++ w) = w := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat_def]
  | succ j ih => simpa [BoolCircuit.encodeNat_def, List.replicate_succ] using ih

/-- `1ʲ0w` has a `0`. -/
theorem hasFalse_encodeNat (j : ℕ) (w : List Bool) :
    hasFalse (BoolCircuit.encodeNat j ++ w) = true := by
  induction j with
  | zero => simp [BoolCircuit.encodeNat_def]
  | succ j ih => simpa [BoolCircuit.encodeNat_def, List.replicate_succ] using ih

/-- A word with a `0` is `1ʲ0w` for `1ʲ = uHead`, `w = uRest`. -/
theorem eq_encodeNat_of_hasFalse {w : List Bool} (h : hasFalse w = true) :
    w = BoolCircuit.encodeNat (uHead w).length ++ uRest w := by
  induction w with
  | nil => simp at h
  | cons b w ih =>
    cases b
    · simp [BoolCircuit.encodeNat_def]
    · simp only [hasFalse_cons, Bool.not_true, Bool.false_or] at h
      have := ih h
      simp only [uHead_true_cons, uRest_true_cons, List.length_cons, BoolCircuit.encodeNat_def,
        List.replicate_succ, List.cons_append] at this ⊢
      exact congrArg _ this

/-- `uRest w` is no longer than `w`. -/
theorem length_uRest_le (w : List Bool) : (uRest w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp
    · simp only [uRest_true_cons, List.length_cons]; omega

/-- `uHead w` is no longer than `w`. -/
theorem length_uHead_le (w : List Bool) : (uHead w).length ≤ w.length := by
  induction w with
  | nil => simp
  | cons b w ih =>
    cases b
    · simp
    · simp only [uHead_true_cons, List.length_cons]; omega

/-- `uHead` is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_uHead : PolyTimeComputable uHead :=
  polyTimeComputable_transduce headδ headO true

/-- `uRest` is polynomial-time (a one-pass transducer). -/
theorem polyTimeComputable_uRest : PolyTimeComputable uRest :=
  polyTimeComputable_transduce restδ restO false

/-- `hasFalse` is polynomial-time (negate, then test for a `1`). -/
theorem polyTimeComputable_hasFalse : PolyTimeComputable (fun w => [hasFalse w]) := by
  have hneg : PolyTimeComputable (transduce (σ := Unit) (fun _ _ => ()) (fun _ b => some !b) ()) :=
    polyTimeComputable_transduce _ _ ()
  have heq : ∀ w : List Bool,
      transduce (σ := Unit) (fun _ _ => ()) (fun _ b => some !b) () w = w.map not := by
    intro w
    induction w with
    | nil => exact transduce_nil _ _ _
    | cons b w ih => simp [transduce_nil, transduce_cons, ih]
  convert polyTimeComputable_any.comp hneg using 1
  funext w
  simp [hasFalse, heq]

/-! ### Lookup in a list of words -/

/-- The entry of index `|J|` of the list encoded in `L`, on `⟨J, L⟩` (`[]` past the end). -/
def getW (z : List Bool) : List Bool := pairFstD (pairSndD (forLoop pairSndD z))

/-- Peeling `j` entries of an encoded list. -/
theorem iterate_pairSndD_encWords (L : List (List Bool)) (j : ℕ) :
    pairSndD^[j] (encWords L) = encWords (L.drop j) := by
  induction j generalizing L with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply]
    cases L with
    | nil =>
      rw [List.drop_nil, encWords_nil, pairSndD_of_pairDecode_eq_none Turing.pairDecode_nil]
      exact iterate_pairSndD_nil j
    | cons w L => simp [ih]

/-- **Lookup**: `getW ⟨J, [w₀, …]⟩ = w_{|J|}` (`[]` past the end). -/
theorem getW_pairEncode (J : List Bool) (L : List (List Bool)) :
    getW (pairEncode J (encWords L)) = L.getD J.length [] := by
  rw [getW, forLoop_pairEncode, pairSndD_pairEncode, iterate_pairSndD_encWords,
    List.getD_eq_getElem?_getD, ← List.head?_drop]
  cases L.drop J.length with
  | nil => rw [encWords_nil, pairFstD_of_pairDecode_eq_none Turing.pairDecode_nil]; rfl
  | cons w L' => simp

/-- Lookup in a list of binary numbers: the value of the entry, `0` past the end. -/
theorem getW_pairEncode_bits (J : List Bool) (vs : List ℕ) :
    getW (pairEncode J (encWords (vs.map Nat.bits))) = Nat.bits (vs.getD J.length 0) := by
  rw [getW_pairEncode]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vs[J.length]? <;> simp [Nat.zero_bits]

/-- Lookup is polynomial-time. -/
theorem polyTimeComputable_getW : PolyTimeComputable getW := by
  have hl : PolyTimeComputable (forLoop pairSndD) := by
    refine polyTimeComputable_forLoop polyTimeComputable_pairSndD 1 1 (fun c d j _ => ?_)
    have := length_iterate_pairSndD_le d j
    simp [length_pairEncode]
    omega
  exact polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hl)

/-! ### Equality, unary multiplication and cutting into blocks -/

/-- Either both projections are empty or the word is the pair of its projections. -/
private theorem pair_cases (z : List Bool) :
    (pairFstD z = [] ∧ pairSndD z = []) ∨ z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => left; simp [pairFstD_eq, pairSndD_eq, hd]
  | some ab =>
    right
    obtain ⟨a, b⟩ := ab
    simpa [pairFstD_eq, pairSndD_eq, hd] using eq_pairEncode_of_pairDecode z a b hd

/-- Word equality on `⟨a, b⟩`: equal lengths and equal values. -/
def eqW (z : List Bool) : Bool :=
  decide ((pairFstD z).length = (pairSndD z).length) && beq z

/-- `eqW ⟨a, b⟩` decides `a = b`. -/
theorem eqW_pairEncode (a b : List Bool) : eqW (pairEncode a b) = decide (a = b) := by
  simp only [eqW, beq_def, pairFstD_pairEncode, pairSndD_pairEncode]
  by_cases h : a = b
  · simp [h]
  · simp only [h, decide_false, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    by_contra hc
    push_neg at hc
    exact h (eq_of_bitsVal_eq hc.1 hc.2)

/-- Word equality is polynomial-time. -/
theorem polyTimeComputable_eqW : PolyTimeComputable (fun z => [eqW z]) :=
  polyTimeComputable_and polyTimeComputable_lenEq polyTimeComputable_beq

/-- One round of unary multiplication on `⟨b, acc⟩`: append `b` to `acc`. -/
private def mulUStep (d : List Bool) : List Bool :=
  pairEncode (pairFstD d) (pairSndD d ++ pairFstD d)

/-- Unary multiplication: on `⟨a, b⟩`, `|a|` copies of `b`. -/
def mulU (z : List Bool) : List Bool :=
  pairSndD (pairSndD (forLoop mulUStep (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))

/-- The rounds of unary multiplication. -/
private theorem iterate_mulUStep (b acc : List Bool) (j : ℕ) :
    mulUStep^[j] (pairEncode b acc) = pairEncode b (acc ++ (List.replicate j b).flatten) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    simp [mulUStep, List.replicate_succ', List.flatten_append]

/-- `|mulU ⟨a, b⟩| = |a| · |b|`. -/
theorem length_mulU (a b : List Bool) : (mulU (pairEncode a b)).length = a.length * b.length := by
  simp [mulU, forLoop_pairEncode, iterate_mulUStep, List.length_flatten, List.sum_replicate]

/-- Unary multiplication is polynomial-time. -/
theorem polyTimeComputable_mulU : PolyTimeComputable mulU := by
  have hs : PolyTimeComputable mulUStep :=
    polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_pairSndD.append
      polyTimeComputable_pairFstD)
  have hl := polyTimeComputable_forLoop hs 3 2 (forLoop_bound_of_ctx 2
    (fun d => by simp [mulUStep]) (fun d => by
      rcases pair_cases d with ⟨h1, h2⟩ | h
      · simp [mulUStep, h1, h2, length_pairEncode]
      · obtain ⟨a, b, rfl⟩ : ∃ a b, d = pairEncode a b := ⟨_, _, h⟩
        simp [mulUStep, length_pairEncode]; omega))
  exact polyTimeComputable_slot3.comp (hl.comp (polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))))

/-- One round of cutting on `⟨c, ⟨rest, acc⟩⟩`: move the first `|c|` bits of `rest` to a new
entry of the word list `acc`; fixed once `rest` is empty. -/
private def chunkStep (d : List Bool) : List Bool :=
  if isNilB (pairFstD (pairSndD d)) then d
  else pairEncode (pairFstD d)
    (pairEncode (PrefixByLength.drop (pairEncode (pairFstD d) (pairFstD (pairSndD d))))
      (pairSndD (pairSndD d) ++
        pairEncode (PrefixByLength.take (pairEncode (pairFstD d) (pairFstD (pairSndD d)))) []))

/-- Cutting `w` into blocks of `|c|` bits, on `⟨c, w⟩`; the result is a word list. -/
def chunkW (z : List Bool) : List Bool :=
  pairSndD (pairSndD (pairSndD (forLoop chunkStep
    (pairEncode (pairSndD z) (pairEncode (pairFstD z) (pairEncode (pairSndD z) []))))))

/-- The first `N` blocks of `c` bits of `w`. -/
def chunkList (c : ℕ) (w : List Bool) (N : ℕ) : List (List Bool) :=
  (List.range N).map fun i => (w.drop (i * c)).take c

/-- A round of cutting on a genuine state. -/
private theorem chunkStep_pairEncode (c rest acc : List Bool) :
    chunkStep (pairEncode c (pairEncode rest acc)) = if rest = [] then
      pairEncode c (pairEncode rest acc) else pairEncode c (pairEncode (rest.drop c.length)
        (acc ++ pairEncode (rest.take c.length) [])) := by
  simp [chunkStep, isNilB_def, PrefixByLength.take_def, PrefixByLength.drop_def]

/-- `N` rounds of cutting a word of `N` blocks. -/
private theorem iterate_chunkStep (c : List Bool) :
    ∀ (N : ℕ) (w : List Bool) (L : List (List Bool)), w.length = N * c.length →
      (0 < c.length ∨ N = 0) → chunkStep^[N] (pairEncode c (pairEncode w (encWords L))) =
        pairEncode c (pairEncode [] (encWords (L ++ chunkList c.length w N)))
  | 0, w, L, h, _ => by simp_all [chunkList]
  | N + 1, w, L, h, hc => by
    have hc' : 0 < c.length := by omega
    have hw : w ≠ [] := by rintro rfl; simp at h; simp [h] at hc'
    rw [Function.iterate_succ_apply, chunkStep_pairEncode, if_neg hw,
      ← encWords_append_singleton,
      iterate_chunkStep c N _ _ (by simp [h, Nat.succ_mul]) (Or.inl hc')]
    congr 3
    simp only [chunkList, List.range_succ_eq_map, List.map_cons, List.map_map, zero_mul,
      List.drop_zero, List.append_assoc, List.singleton_append]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- **Cutting into blocks**: if `|w| = N·|c|` then `chunkW ⟨c, w⟩` lists the `N` blocks. -/
theorem chunkW_pairEncode (c w : List Bool) (N : ℕ) (h : w.length = N * c.length)
    (hc : 0 < c.length ∨ N = 0) :
    chunkW (pairEncode c w) = encWords (chunkList c.length w N) := by
  have hN : N ≤ w.length := by
    rcases hc with hc | rfl
    · rw [h]; exact Nat.le_mul_of_pos_right _ hc
    · exact Nat.zero_le _
  have he := iterate_chunkStep c N w [] h hc
  simp only [encWords_def, List.flatMap_nil, List.nil_append] at he
  simp only [chunkW, pairFstD_pairEncode, pairSndD_pairEncode, forLoop_pairEncode]
  rw [show w.length = (w.length - N) + N by omega, Function.iterate_add_apply, he,
    Function.iterate_fixed (by rw [chunkStep_pairEncode, if_pos rfl])]
  simp [encWords_def]

/-- Cutting is polynomial-time.

**Proof sketch.** The round is assembled from the projections, the prefix operations and
`polyTimeComputable_ite`; it keeps `c` and grows a genuine state by `2` bits (the moved bits
are re-encoded once), so `forLoop_bound_of_ctx` bounds the counted loop. -/
theorem polyTimeComputable_chunkW : PolyTimeComputable chunkW := by
  have hcr := polyTimeComputable_pairFstD.pairEncode polyTimeComputable_slot2
  have hs : PolyTimeComputable chunkStep := by
    unfold chunkStep
    exact polyTimeComputable_ite (by
        simpa only [Function.comp_def, isNilB_def] using
          polyTimeComputable_isNil.comp polyTimeComputable_slot2)
      polyTimeComputable_id (polyTimeComputable_pairFstD.pairEncode
        ((polyTimeComputable_dropPrefixByLength.comp hcr).pairEncode
          (polyTimeComputable_slot3.append
            ((polyTimeComputable_takePrefixByLength.comp hcr).pairEncode
              (polyTimeComputable_const [])))))
  have hctx : ∀ d, pairFstD (chunkStep d) = pairFstD d := fun d => by
    unfold chunkStep; split_ifs <;> simp
  have hlen : ∀ d, (chunkStep d).length ≤ d.length + 2 * ((pairFstD d).length + 1) := by
    intro d
    by_cases hr : pairFstD (pairSndD d) = []
    · simp [chunkStep, isNilB_def, hr]
    rcases pair_cases d with ⟨-, h2⟩ | h
    · simp [h2, pairFstD_eq, Turing.pairDecode_nil] at hr
    obtain ⟨c, S, rfl⟩ : ∃ c S, d = pairEncode c S := ⟨_, _, h⟩
    simp only [pairSndD_pairEncode] at hr
    rcases pair_cases S with ⟨h1, -⟩ | hS
    · exact absurd h1 hr
    obtain ⟨rest, acc, rfl⟩ : ∃ a b, S = pairEncode a b := ⟨_, _, hS⟩
    simp only [pairFstD_pairEncode] at hr
    rw [chunkStep_pairEncode, if_neg hr]
    simp only [length_pairEncode, List.length_append, List.length_drop, List.length_take,
      List.length_nil, pairFstD_pairEncode]
    omega
  have hl := polyTimeComputable_forLoop hs 3 2 (forLoop_bound_of_ctx 2 hctx hlen)
  exact (polyTimeComputable_pairSndD.comp polyTimeComputable_slot3).comp
    (hl.comp (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])))))

end BinArith

end Complexity
```


## ===== TCSlib/Cryptography/Hashing/SIS/Universality.lean =====

```text
/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Basic
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.InformationTheory.LeftoverHash

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Universality and extraction for the existing binary matrix hash

## Main definitions

This module reuses `hash` without defining a second binary matrix hash.

## Main results

Distinct binary inputs have a uniform hash difference even over composite moduli.
The resulting collision universality gives a strong, seed-published leftover-hash
bound with explicit dimension and sample parameters.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Equation (4.1.1) and Section 5.2.1 (the binary linear extractor in Regev encryption).
* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.

No SIS or LWE hardness assumption is used here; the SIS norm field is irrelevant.
The family is collision-universal, not pairwise independent: its zero input always
hashes to zero. The proofs use the owner-side universality and min-entropy
equivalences to apply the strong leftover-hash lemma.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open TCSlib.InformationTheory
open TCSlib.Cryptography.SIS (Parameters)

/-- Distinct binary inputs have an exactly uniform modular hash difference for a
uniform matrix [Pei16, Section 5.2.1, regularity argument].

**Proof sketch.** Choose a differing input coordinate. Its integer difference is
`1` or `-1`, hence a unit modulo every allowed modulus. Split the matrix into this
column and the other columns. Once the other columns are fixed, multiplying the
chosen column by the unit and translating is a bijection. Average the resulting
singleton probability over the other columns. The differing coordinate exists
whenever the inputs are distinct, so the empty-column case is vacuous. -/
theorem hash_difference_probability (P : Parameters) (x y : Fin P.columns → Bool)
    (hxy : x ≠ y) (z : Fin P.dimension → ZMod P.modulus) :
    uprob (fun A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) =>
      hash P A x - hash P A y = z) = 1 / (P.modulus : ℝ) ^ P.dimension := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  let difference : Fin P.columns → ZMod P.modulus :=
    fun k => ((x k).toNat : ZMod P.modulus) - ((y k).toNat : ZMod P.modulus)
  have hpivot : difference j = 1 ∨ difference j = -1 := by
    cases hx : x j <;> cases hy : y j <;> simp_all [difference]
  have hunit : IsUnit (difference j) := by
    rcases hpivot with h | h
    · rw [h]
      exact isUnit_one
    · rw [h]
      exact isUnit_neg_one
  obtain ⟨unit, hunit⟩ := hunit
  let Column := Fin P.dimension → ZMod P.modulus
  let Other := {k : Fin P.columns // k ≠ j} → Column
  let split : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ≃ Other × Column :=
    (Equiv.piComm (fun _ _ => ZMod P.modulus)).trans
      ((Equiv.funSplitAt j Column).trans (Equiv.prodComm Column Other))
  -- For fixed other columns the difference is a unit scaling followed by a translation.
  let move (a : Other) : Equiv.Perm Column :=
    (Equiv.piCongrRight (fun _ : Fin P.dimension => unit.mulRight)).trans
      (Equiv.addRight (fun i => ∑ k : {k : Fin P.columns // k ≠ j}, a k i * difference k))
  have hhash (A : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)) :
      hash P A x - hash P A y = move (split A).1 (split A).2 := by
    rw [hash_eq, hash_eq, ← Matrix.mulVec_sub]
    funext i
    change (∑ k, A i k * difference k) =
      A i j * (unit : ZMod P.modulus) + ∑ k : {k : Fin P.columns // k ≠ j}, A i k * difference k
    rw [hunit]
    exact Fintype.sum_eq_add_sum_subtype_ne _ j
  have huniform : uprob (fun c : Column => c = z) = 1 / (P.modulus : ℝ) ^ P.dimension := by
    rw [uprob_eq_card_filter]
    have hfilter : Finset.univ.filter (fun c : Column => c = z) = {z} := by
      ext c
      simp
    rw [hfilter, Finset.card_singleton]
    change ((1 : ℕ) : ℝ) / (Fintype.card (Fin P.dimension → ZMod P.modulus) : ℝ) = _
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_one, Nat.cast_pow]
  have hsection (a : Other) :
      uprob (fun c : Column => move a c = z) = 1 / (P.modulus : ℝ) ^ P.dimension :=
    (uprob_comp_equiv (move a) (· = z)).trans huniform
  -- Every choice of the other columns gives the same singleton probability.
  rw [← uprob_comp_equiv split.symm (fun A => hash P A x - hash P A y = z), uprob_prod]
  simp only [hhash, Equiv.apply_symm_apply, hsection, uexp_def, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The existing binary matrix hash is collision-universal over every allowed modulus
[Pei16, Section 5.2.1; Vad12, Theorem 6.18].

**Proof sketch.** Specialize the uniform-difference equation to zero, rewrite equality
as zero difference, and convert the probability equation to the owner's collision
count bound. No field structure, norm bound or hardness assumption is used. -/
theorem isUniversal_hash (P : Parameters) : IsUniversal (hash P) := by
  classical
  refine (isUniversal_iff (hash P)).2 ?_
  intro x y hxy
  let Key := Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)
  have hprob : uprob (fun A : Key => hash P A x = hash P A y) =
      1 / (P.modulus : ℝ) ^ P.dimension := by
    simpa only [sub_eq_zero] using hash_difference_probability P x y hxy 0
  rw [uprob_eq_card_filter] at hprob
  have hkeys : (Fintype.card Key : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have houtputs : (Fintype.card (Fin P.dimension → ZMod P.modulus) : ℝ) =
      (P.modulus : ℝ) ^ P.dimension := by
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow]
  rw [houtputs]
  apply le_of_eq
  calc
    _ = (1 / (P.modulus : ℝ) ^ P.dimension) * Fintype.card Key :=
      (div_eq_iff hkeys).mp hprob
    _ = _ := by rw [one_div, mul_comm, ← div_eq_mul_inv]

/-- The full uniform distribution on binary words of length `m` has min-entropy `m`
[Vad12, Section 6.1, exact finite uniform specialization].

**Proof sketch.** Every word has probability `1/2^m` by the public uniform probability
equation and the finite function-space cardinality. This is `2^(-m)` over the reals. -/
theorem uniform_bits_hasMinEntropy (m : ℕ) :
    FinDist.HasMinEntropy (FinDist.uniform (Fin m → Bool)) (m : ℝ) := by
  refine (FinDist.hasMinEntropy_iff _ _).2 ?_
  intro r
  rw [FinDist.uniform_apply, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    Nat.cast_pow, Nat.cast_ofNat, Real.rpow_neg (by norm_num), Real.rpow_natCast]

/-- Publishing the uniform hash seed retains a statistical extraction error at most
`sqrt(q^dimension / 2^columns)/2` [Pei16, Section 5.2.1; Vad12, Theorem 6.18].

**Proof sketch.** Apply the existing strong leftover-hash lemma to `isUniversal_hash`
and uniform binary min-entropy. Evaluate the modular-vector cardinality and convert
the real negative power into division by the positive binary power. -/
theorem strong_leftover_hash (P : Parameters) :
    statDist (hashPair (hash P) (FinDist.uniform (Fin P.columns → Bool)))
      (FinDist.uniform
        (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
          (Fin P.dimension → ZMod P.modulus))) ≤
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
  classical
  simpa only [Fintype.card_fun, Fintype.card_fin, ZMod.card, Nat.cast_pow,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast, div_eq_mul_inv]
    using leftover_hash (isUniversal_hash P) (uniform_bits_hasMinEntropy P.columns)

/-- Any independently randomized test of the seed-published hash has at most the
strong leftover-hash distinguishing error [Pei16, Section 5.2.1].

**Proof sketch.** For each target pair, the sampler fiber is the product of its
singleton key and the matching subset words. Sum the uniform mass over this
product to recover the public `hashPair` equation. The ideal sampler has a
singleton fiber. Apply the advantage bound for independently randomized tests
and the strong leftover-hash theorem. -/
theorem distAdv_hash_uniform_le {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : Parameters)
    (D : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      (Fin P.dimension → ZMod P.modulus)) → ρ → Bool) :
    distAdv (fun r : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
      (Fin P.columns → Bool) => (r.1, hash P r.1 r.2))
      (id : (Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) ×
        (Fin P.dimension → ZMod P.modulus)) → _) D ≤
      (1 / 2) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) := by
  classical
  let Key := Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus)
  let Input := Fin P.columns → Bool
  let Output := Fin P.dimension → ZMod P.modulus
  let View := Key × Output
  let sampler (r : Key × Input) : View := (r.1, hash P r.1 r.2)
  have hmap : (FinDist.uniform (Key × Input)).map sampler =
      hashPair (hash P) (FinDist.uniform Input) := by
    apply FinDist.ext
    rintro ⟨A, y⟩
    have hfilter : (Finset.univ.filter fun r : Key × Input => sampler r = (A, y)) =
        ({A} : Finset Key) ×ˢ (Finset.univ.filter fun x : Input => hash P A x = y) := by
      apply Finset.ext
      intro r
      rw [Finset.mem_filter, Finset.mem_product]
      simp only [Finset.mem_univ, true_and, Finset.mem_singleton, Finset.mem_filter]
      change (r.1, hash P r.1 r.2) = (A, y) ↔ _
      rw [Prod.mk.injEq]
      constructor
      · rintro ⟨hA, hy⟩
        exact ⟨hA, by simpa only [hA] using hy⟩
      · rintro ⟨hA, hy⟩
        exact ⟨hA, by simpa only [hA]⟩
    rw [FinDist.map_apply, hashPair_apply, hfilter, Finset.sum_product, Finset.sum_singleton,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [FinDist.uniform_apply, Fintype.card_prod, Nat.cast_mul, mul_inv_rev, mul_comm, Key]
  have hideal : (FinDist.uniform View).map (id : View → View) = FinDist.uniform View := by
    apply FinDist.ext
    intro z
    rw [FinDist.map_apply]
    have hfilter : (Finset.univ.filter fun r : View => id r = z) = {z} := by
      ext r
      simp only [id_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    rw [hfilter, Finset.sum_singleton]
  have h := distAdv_le_statDist sampler (id : View → View) D
  rw [hmap, hideal] at h
  exact h.trans (strong_leftover_hash P)

/-- A residue width and `2κ` entropy slack give an explicit exponentially small
extraction error [Pei16, Section 5.2.1, quantitative repository refinement].

**Proof sketch.** Bound `q^dimension` by `2^(dimension*width)`. The sample budget
then bounds the ratio by `2^(-2κ)`, the square of the desired nonnegative bound
before the factor of one half. Compare the square root with that bound, including
parameter zero and empty output dimension. -/
theorem leftover_error_le (P : Parameters) (width κ : ℕ)
    (hq : P.modulus ≤ 2 ^ width) (hm : P.dimension * width + 2 * κ ≤ P.columns) :
    (1 / 2 : ℝ) * Real.sqrt ((P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns) ≤
      (1 / 2 : ℝ) * ((2 : ℝ)⁻¹) ^ κ := by
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hwidth : (P.modulus : ℝ) ≤ (2 : ℝ) ^ width := by exact_mod_cast hq
  have hnum : (P.modulus : ℝ) ^ P.dimension ≤ (2 : ℝ) ^ (P.dimension * width) := by
    rw [Nat.mul_comm P.dimension width, pow_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hwidth _
  have hratio : (P.modulus : ℝ) ^ P.dimension / (2 : ℝ) ^ P.columns ≤
      1 / (2 : ℝ) ^ (2 * κ) := by
    apply (div_le_div_iff₀ (pow_pos htwo _) (pow_pos htwo _)).2
    rw [one_mul]
    calc
      _ ≤ (2 : ℝ) ^ (P.dimension * width) * (2 : ℝ) ^ (2 * κ) :=
        mul_le_mul_of_nonneg_right hnum (pow_nonneg htwo.le _)
      _ = (2 : ℝ) ^ (P.dimension * width + 2 * κ) := by rw [pow_add]
      _ ≤ (2 : ℝ) ^ P.columns := pow_le_pow_right₀ (by norm_num) hm
  have hsquare : 1 / (2 : ℝ) ^ (2 * κ) = (((2 : ℝ)⁻¹) ^ κ) ^ 2 := by
    rw [one_div, ← inv_pow, ← pow_mul, Nat.mul_comm 2 κ]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.sqrt_le_iff.mpr ⟨pow_nonneg (inv_nonneg.mpr htwo.le) _, hratio.trans_eq hsquare⟩

end TCSlib.Cryptography.Hashing.SIS
```


## ===== audits/lwe-sis-counted-loop-consumer-proofs-resolutions.md =====

```text
# Gate 15 audit disposition

Gate 15 round one **passes the seven efficiency proofs and two asymptotic
SIS collision-resistance proofs** with zero blockers, zero majors, one
documentation minor, and four continuing notes. The auditor replayed all
144 modules and both probes with matching outputs, the Gate 14 envelope
probe, and 22 supplementary Lean guards.
[Findings](lwe-sis-counted-loop-consumer-proofs-findings.md) · [Intake receipt](../briefs/lwe-sis-constructions/fills/10-counted-loop-consumers/review-intake.json)

Intake rehashed all six published packet files, five outer checksums, 42
nested checksums and 228 indexed sections. It reproduced the GitHub merge
preview at target `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` and audited
draft `e1614b8466eb74f8842b3d6f244ca4ff3bfe1720`. The preview tree
`1da91a108d0efc2e347ba8ef913077b920b93624` preserves the audited
library, root exports, H16 registry, and build pins.
[Published packet](https://github.com/Shilun-Allan-Li/tcslib/tree/be2117f662dc51da335bebf70c90f14521f8076b/lwe-sis-constructions/outbox/gates/15-counted-loop-consumer-proofs-r1)

| ID | Disposition |
|---|---|
| F01 | Corrected the proof report. The nine Gate 13 entries already contained the three standard axioms. Each Gate 15 fill removes only `sorryAx`. The audit packet retains the original report at its records pin. |
| N01 | Closed all nine campaign admissions. Track the 17 inherited warnings with the existing machine library. |
| N02 | Integrated the 84 approved PW10, Pei16, and Wu24 attributions and the approved reference changes. Three earlier foundation attributions carry forward. |
| N03 | Track efficient trapdoor recovery, family-level sampling and security, the generic SIS primitive bridge, strong one-time signatures, and the final CPA and CCA2 bridges separately. |
| N04 | The local exact-target preview passed all 1,089 root-reachable modules and the export checks. Compare the live merge preview after publication. |

The user approved the scoped source updates and performs merges.
[Landing verification](../briefs/lwe-sis-constructions/landing/05-construction-statements/LANDING.md)
```


## ===== briefs/lwe-sis-constructions/landing/05-construction-statements/LANDING.md =====

```text
# Exact-target landing verification for draft #250

Gate 15 passed the seven efficiency proofs and two asymptotic SIS
collision-resistance proofs. The independent review reproduced all 144
campaign module logs and both probes. F01 corrects the axiom description
to the removal of `sorryAx` alone.
[Audit disposition](../../../../audits/lwe-sis-counted-loop-consumer-proofs-resolutions.md)

| Pin | Revision |
|---|---|
| Target `cryptography/lwe-sis-constructions` | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| Checked Lean source and root | `8b3187bdaf0c634c086313a727a7210dca14bfeb` |
| Checked source records head | `ecbef871d2f7b878eb71b118b95fd24d5bbcde7c` |
| Exact-target preview tree | `9b0e3b5c6e6b373d17fc596df5173dc8201aa548` |

The preview preserves the Gate 15 library, root exports, H16 registry,
Lean toolchain and Lake pins. All 25 added Lean paths are reachable from
`TCSlib.lean`. The whole-library closure includes 1,089 modules
including that root. The 34 existing unexported Lean paths are outside
the root closure.

| Check | Result |
|---|---|
| Whole-library elaboration | All 1,089 modules produced fresh objects with zero errors in 4452.863 s of summed module time. |
| Admission diagnostics | Zero campaign-owned admissions. The whole library has 198 inherited admission warnings across 47 modules, including the 17 from the Gate 15 closure. Every affected file is byte-identical to the exact target. |
| Package bootstrap | Lean 4.25.0. Reused 2,513 reachable pinned package objects, restored 1,093 from local cache archives, and checked 31 PFR dependencies from the pinned source. |
| Dataset hygiene | Strict validation passed with zero hard failures. |
| Blueprint | Strict output matches the target byte for byte, including 857 inherited orphan labels. The check passes with those orphans allowed. |

The isolated object tree began without project objects. The first retry
supplied missing package companion files. The inherited
`Complexity/ClassP/BinaryArith/DetMod` timed out at 300 s and passed
with a longer limit in 735.923 s. All 45 modules
in its project closure are byte-identical to the exact target. While it
retried, the remaining independent modules ran serially in the same
object tree. The nine dependent modules finished afterward, ending with
`TCSlib.lean`.
The diagnostic log is preserved as a gzip archive. The landing receipt
records its decompressed SHA-256.
[Landing receipt](landing-checks.json) · [Module receipts](evidence/whole-library-checks.json) · [Checksums](evidence/SHA256SUMS)

The approved source integration covers 35 PW10 attributions and 49 Pei16
and Wu24 attributions. Three prior foundation attributions carry forward.
[PW10 approval](pw10-source-approval.json) · [Pei16 and Wu24 approval](pei16-wu24-source-approval.json)

The final publication check compares the live GitHub merge preview with
the verified library and source records on this draft. The user performs
the merge.
```


## ===== blueprint/src/references/peikert2016-lattice-survey.md =====

```text
<!-- generated-by: Codex source review of approved excerpts -->
<!-- source-pdf-sha256: 1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488 -->
<!-- validation-status: scoped excerpts for PRs #236 and #237 -->

# A Decade of Lattice Cryptography

Chris Peikert, author version dated 17 February 2016.

The approved coverage is Definitions 4.1.1, 4.2.1 and 4.2.3, with the
introductory sentence specifying the LWE error law. The anchors refer to
pages 20, 21 and 24 of the original PDF. The added SIS passages cover
the exclusion of trivial modulus multiples and the binary collision argument. The raw extraction retains the
complete document. Footnotes and intervening material are omitted here.

<a id="pdf-1a9802b66031-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.98 -->

**Definition 4.1.1 (Short Integer Solution ($\mathrm{SIS}_{n,q,\beta,m}$)).** Given $m$ uniformly random vectors $\mathbf a_i\in\mathbb Z_q^n$, forming
the columns of a matrix $\mathbf A\in\mathbb Z_q^{n\times m}$, find a nonzero integer vector $\mathbf z\in\mathbb Z^m$ of norm $\|\mathbf z\|\le\beta$ such
that

$$
f_{\mathbf A}(\mathbf z):=\mathbf A\mathbf z=\sum_i\mathbf a_i\cdot z_i=\mathbf0\in\mathbb Z_q^n.\tag{4.1.1}
$$

<a id="pdf-1a9802b66031-p020-b002"></a>
<!-- pdf-source: page=20; block=2; confidence=0.98 -->

**Observation after Equation (4.1.1).**

Similarly, we
  must take $\beta<q$ because otherwise $\mathbf z=(q,0,\ldots,0)\in\mathbb Z^m$ would always be a legitimate (but trivial)
  solution.

<a id="pdf-1a9802b66031-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.98 -->

* Any solution for a matrix $\mathbf A$ can trivially be converted to one for any extension $[\mathbf A\mid\mathbf A']$, simply by
  appending the solution vector with zeros (which leaves the norm of the solution unchanged). In other
  words, we can ignore columns $\mathbf a_i$ as desired, so the SIS problem can only become easier as $m$ increases.
  Similarly, it can only become harder as $n$ increases.

* The norm bound $\beta$ and the number $m$ of vectors $\mathbf a_i$ must be large enough that a solution is guaranteed
  to exist. This is the case whenever $\beta\ge\sqrt{\bar m}$ and $m\ge\bar m$, where $\bar m$ is the smallest integer greater than
  $n\log q$, by a pigeonhole argument: first, by the previous observation we can assume without loss of
  generality that $m=\bar m$. Then because there are more than $q^n$ vectors $\mathbf x\in\{0,1\}^m$, there must be two
  distinct $\mathbf x,\mathbf x'$ such that $\mathbf A\mathbf x=\mathbf A\mathbf x'\in\mathbb Z_q^n$, so their difference $\mathbf z=\mathbf x-\mathbf x'\in\{0,\pm1\}^m$ is a solution of
  norm at most $\beta$.

* The above pigeonhole argument in fact shows more: the induced function family $\{f_{\mathbf A}:\{0,1\}^m\to\mathbb Z_q^n\}$
  defined in Equation (4.1.1) is *collision resistant*, assuming the hardness of the corresponding SIS
  problem. This is because a collision $\mathbf x,\mathbf x'\in\{0,1\}^m$ for $f_{\mathbf A}$ immediately yields an SIS solution for $\mathbf A$.
  (Of course the domain $\{0,1\}^m$ is somewhat arbitrary here, and can be replaced by essentially any other
  large enough set of sufficiently short integer vectors.)

<a id="pdf-1a9802b66031-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.98 -->

LWE is parameterized by positive integers $n$ and $q$, and an error distribution $\chi$ over $\mathbb Z$.

**Definition 4.2.1 (LWE distribution).** For a vector $\mathbf s\in\mathbb Z_q^n$ called the *secret*, the LWE distribution $A_{\mathbf s,\chi}$
over $\mathbb Z_q^n\times\mathbb Z_q$ is sampled by choosing $\mathbf a\in\mathbb Z_q^n$ uniformly at random, choosing $e\leftarrow\chi$, and outputting
$(\mathbf a,b=\langle\mathbf s,\mathbf a\rangle+e\bmod q)$.

*Definition 4.2.2 omitted.*

**Definition 4.2.3 (Decision-$\mathrm{LWE}_{n,q,\chi,m}$).** Given $m$ independent samples $(\mathbf a_i,b_i)\in\mathbb Z_q^n\times\mathbb Z_q$ where every
sample is distributed according to either: (1) $A_{\mathbf s,\chi}$ for a uniformly random $\mathbf s\in\mathbb Z_q^n$ (fixed for all samples), or
(2) the uniform distribution, distinguish which is the case (with non-negligible advantage).

<a id="pdf-1a9802b66031-p036-b001"></a>
<!-- pdf-source: page=36; block=1; confidence=1.00 -->

**Section 5.1, SIS hashing.** The opening paragraph recalls that the
binary matrix map of Equation (4.1.1) is collision resistant under the
hardness of the corresponding SIS problem. A collision yields the short
nonzero difference described in the earlier section.

<a id="pdf-1a9802b66031-p037-b001"></a>
<!-- pdf-source: page=37; block=1; confidence=1.00 -->

**Section 5.2.1, Regev public-key encryption.** The public key collects
LWE samples under a uniform common secret as columns of an augmented
matrix. Equation (5.2.1) gives the augmented matrix and Equation (5.2.2)
cancels the secret product to expose the errors. Equation (5.2.3) forms
a binary subset sum and adds the message's half-modulus codepoint to its
last coordinate. Decryption cancels the secret contribution and compares
the residual with the two codepoints modulo the modulus.

<a id="pdf-1a9802b66031-p038-b001"></a>
<!-- pdf-source: page=38; block=1; confidence=1.00 -->

**Section 5.2.1, correctness.** The accumulated integer error is the
inner product of the key error vector and the binary subset. The source
uses a quarter-modulus separation and discusses choosing the noise law
and modulus to make decryption correct with overwhelming probability.

<a id="pdf-1a9802b66031-p038-b002"></a>
<!-- pdf-source: page=38; block=2; confidence=1.00 -->

**Section 5.2.1, first security hybrid.** Compare the fixed-bit view
of the public key and ciphertext with the experiment that uses a uniform
public key. A decision-LWE test forms its challenge matrix, encrypts the
fixed bit, and runs the view distinguisher. The simulation is exact for
both challenge laws.

<a id="pdf-1a9802b66031-p038-b003"></a>
<!-- pdf-source: page=38; block=3; confidence=1.00 -->

**Section 5.2.1, second security hybrid.** For a uniform augmented
key matrix and an independent uniform binary subset, the leftover hash
lemma makes the seed-published matrix product close to a uniform independent
ciphertext. Adding a fixed message vector preserves that ideal uniform law.
This hybrid and the first hybrid compare the two fixed-bit views.
```


## ===== blueprint/src/references/wu2024-topics-cryptography.md =====

```text
<!-- generated-by: Codex source review of scoped excerpts -->
<!-- source-pdf-sha256: c0f87bf2e871180d62b2b27d38b916bce1a7b2228dbb68de72341597341d6d87 -->
<!-- validation-status: scoped excerpts for PR #237 -->

# CS 395T Topics in Cryptography

David Wu, Spring 2024 lecture notes. Compilation last updated 30 April 2024.

This excerpt covers Definition 20.5 and its correctness discussion, followed
by the security argument in Lecture 21. The anchors refer to pages 83 and 85
of the original PDF. The accompanying source review records the adaptations
in the formal statements.

<a id="pdf-c0f87bf2e871-p083-b001"></a>
<!-- pdf-source: page=83; block=1; confidence=0.95 -->

**Definition 20.5 (Regev Symmetric Encryption Scheme).** The definition of the scheme follows below:

* $\mathrm{Setup}(1^\lambda)$: Output $s\stackrel R\leftarrow\mathbb Z_q^n$.
* $\mathrm{Encrypt}(s,\mu\in\{0,1\})$: Sample $a\stackrel R\leftarrow\mathbb Z_q^n$ and $e\stackrel R\leftarrow\chi$. Output $\mathrm{ct}=(a,s^Ta+e+\mu\lfloor q/2\rfloor)$
* $\mathrm{Decrypt}(s,\mathrm{ct}=(c_1,c_2))$: Output $\lfloor c_2-s^Tc_1\pmod q\rceil_{q,2}$, where $\lfloor\cdot\rceil$ is the rounding operation and
  $\lfloor x\rceil_{q,2}:=\left\lfloor\frac2q\cdot x\right\rceil$.

**Correctness** Let $\mathrm{ct}=(c_1,c_2)\leftarrow\mathrm{Encrypt}(s,\mu)$. It follows that

$$
\begin{aligned}
\lfloor c_2-s^Tc_1\pmod q\rceil_{q,2}
&=\left\lfloor s^Ta+e+\mu\left\lfloor\frac q2\right\rfloor-s^Ta\pmod q\right\rceil_{q,2}\\
&=\left\lfloor e+\mu\left\lfloor\frac q2\right\rfloor\pmod q\right\rceil_{q,2}\\
&\approx\left\lfloor\frac2q e+\mu\pmod q\right\rceil.
\end{aligned}
$$

Note that if $|e|<q/4$, then we can see that the result of the rounding operation is unchanged by $e$, and thus
rounds to the value $\mu$.

<a id="pdf-c0f87bf2e871-p085-b001"></a>
<!-- pdf-source: page=85; block=1; confidence=0.95 -->

**Security.** The scheme is CPA-secure assuming the hardness of the LWE problem, which we recall here.

**Definition 21.2 (LWE Problem).** Given $a\stackrel R\leftarrow\mathbb Z_q^n$, $e\leftarrow\chi$, $s\stackrel R\leftarrow\mathbb Z_q^n$, $u\stackrel R\leftarrow\mathbb Z_q$, distinguish $(a,s^Ta+e)$ and
$(a,u)$.

By this assumption, in the security argument, we can replace the ciphertexts with $(a,u+\mu\lfloor q/2\rfloor)$. Then,
the encryption scheme becomes a one-time pad.

<a id="pdf-c0f87bf2e871-p086-b001"></a>
<!-- pdf-source: page=86; block=1; confidence=1.00 -->

**Lecture 21, Regev public-key encryption and Definition 21.3.** The
public key contains zero encryptions under one secret. To encrypt, take a
random binary subset and shift its second component by the message
codepoint. Decryption subtracts the secret product. The bounded error law
gives an absolute subset-error bound of $mB$. The formalization uses strict
separation for its chosen decoder.

<a id="pdf-c0f87bf2e871-p086-b002"></a>
<!-- pdf-source: page=86; block=2; confidence=1.00 -->

**Lecture 21, Regev public-key security.** The first comparison replaces
the LWE public key by a uniform matrix and vector. The second uses the
leftover hash lemma for the uniform augmented matrix and binary subset to
hide the fixed message shift statistically.
```


## ===== blueprint/src/references/pass-shelat-2010-ch3.raw.md =====

```text
Chapter 3

Indistinguishability &
Pseudo-Randomness

Recall that one main drawback of the One-time pad encryption
scheme—and its simple encryption operation Enck (m) = m ⊕ k—
is that the key k needs to be as long as the message m. A natural
approach for making the scheme more efficient would be to start
off with a short random key k and then try to use some pseudo-
random generator g to expand it into a longer “random-looking”
key k0 = g(k ), and finally use k0 as the key in the One-time pad.
    Can this be done? We start by noting that there can not exist
pseudo-random generators g that on input k generate a perfectly
random string k0 , as this would contradict Shannon’s theorem
(show this). However, remember that Shannon’s lower bound
relied on the premise that the adversary Eve is computationally
unbounded. Thus, if we restrict our attention to efficient adver-
saries, it might be possible to devise pseudo-random generators
that output strings which are “sufficiently” random-looking for
our encryption application.
    To approach this problem, we must first understand what
it means for a string to be “sufficiently random-looking” to a
polynomial time adversary. Possible answers include:

  — Roughly as many 0 as 1.
  — Roughly as many 00 as 11
  — Each particular bit is roughly unbiased.

                               67
68          chapter 3. indistinguishability & pseudo-randomness


  — Each sequence of bits occurs with roughly the same proba-
    bility.
  — Given any prefix, it is hard to guess the next bit.
  — Given any prefix, it is hard to guess the next sequence.

    All of the above answers are examples of specific statistical
tests—and many more such test exist in the literature. For specific
simulations, it may be enough to use strings that pass some
specific statistical tests. However, for cryptography, we require
the use of strings that pass all (efficient) statistical tests. At first,
it seems quite overwhelming to test a candidate pseudo-random
generator against all efficient tests. To do so requires some more
abstract concepts which we now introduce.


3.1 Computational Indistinguishability
We introduce the notion of computational indistinguishability to for-
malize what it means for two probability distributions to “appear”
the same from the perspective of a computationally bounded test.
This notion is one of the cornerstones of modern cryptography.
To begin our discussion, we present two games that illustrate
important ideas in the notion of indistinguishability.

Game 1 Flip the page and spend no more than two seconds
looking at Fig. 1 that appears on the next page. Do the two boxes
contain the same arrangement of circles?
   Now suppose you repeat the experiment but spend 10 sec-
onds instead of two. Imagine spending 10 minutes instead of 10
seconds. If you are only given a short amount of time, the two
boxes appear indistinguishable from one another. As you take
more and more time to analyze the images, you are able to tease
apart subtle differences between the left and right. Generalizing,
even if two probability distrubutions are completely disjoint, it
may be that an observer who is only given limited processing
time cannot distinguish between the two distributions.

Game 2 A second issue concerns the size of a problem instance.
Consider the following sequence of games parameterized by the
 3.1. Computational Indistinguishability                         69




      Figure 69.1: Are the two boxes the same or different?


 value n in Fig. 2. The point of the game is to determine if the
 number of overlapping boxes is even or odd. An example of each
 case is given on the extreme left. The parameter n indicates the
 number of boxes in the puzzle. Notice that small instances of
 the puzzle are easy to solve, and thus “odd” instances are easily
 distinguishable from “even” ones. However, by considering a
 sequence of puzzles, as n increases, a human’s ability to solve
 the puzzle correctly rapidly approaches 1/2—i.e., no better than
 guessing.
     As our treatment is asymptotic, the actual formalization of
 this notion considers sequences—called ensembles—of probability
 distributions (or growing output length).

.Definition 69.3 (Ensembles of Probability Distributions) A se-
 quence { Xn }n∈N is called an ensemble if for each n ∈ N, Xn is a
 probability distribution over {0, 1}∗ .

    Normally, ensembles are indexed by the natural numbers
 n ∈ N. Thus, for the rest of this book, unless otherwise specified,
 we use { Xn }n to represent such an ensemble.

.Definition 69.4 (Computational Indistinguishability). Let { Xn }n
 and {Yn }n be ensembles where Xn , Yn are distributions over
70             chapter 3. indistinguishability & pseudo-randomness



         evens                    odds
     # of boxes that overlap   # of ... is odd
     another box is even




          (a) Description of Game                (b) n = 9: Even or Odd?




         (c) n = 22: Even or Odd?                (d) n > 80: Even or Odd?

                 Figure 70.2: A game parameterized by n


{0, 1}`(n) for some polynomial `(·). We say that { Xn }n and
{Yn }n are computationally indistinguishable (abbr. { Xn }n ≈ {Yn }n )
if for all non-uniform p.p.t. D (called the “distinguisher”), there
exists a negligible function e(·) such that ∀n ∈ N


      Pr [t ← Xn , D (t) = 1] − Pr [t ← Yn , D (t) = 1] < e(n).


In other words, two (ensembles of) probability distributions are
computationally indistinguishable if no efficient distinguisher D
can tell them apart better than with a negligible advantage.
    To simplify notation, we say that D distinguishes the distribu-
tions Xn and Yn with probability e if


         Pr [t ← Xn , D (t) = 1] − Pr [t ← Yn , D (t) = 1] > e.


Additionally, we say D distinguishes the ensembles { Xn }n and
{Yn }n with probability µ(·) if ∀n ∈ N, D distinguishes Xn and
Yn with probability µ(n).
 3.1. Computational Indistinguishability                            71


 3.1.1   Properties of Computational Indistinguishability
 We highlight some important (and natural) properties of the
 notion of indistinguishability. This properties will be used over
 and over again in the remainder of the course.

 Closure Under Efficient Opertations
 The first property formalizes the statement “If two distributions
 look the same, then they look the same no matter how you pro-
 cess them” (as long as the processing is efficient). More formally,
 if two distributions are indistinguishable, then they remain indis-
 tinguishable even after one applies a p.p.t. computable operation
 to them.

.Lemma 71.5 (Closure Under Efficient Operations) If the pair of
 ensembles { Xn }n ≈ {Yn }n , then for any n.u.p.p.t M, { M ( Xn )}n ≈
 { M(Yn )}n .
 Proof. Suppose there exists a non-uniform p.p.t. D and non-
 negligible function µ(n) such that D distinguishes { M( Xn )}n
 from { M(Yn )}n with probability µ(n). That is,

 | Pr[t ← M( Xn ) : D (t) = 1] − Pr[t ← M(Yn ) : D (t) = 1]| > µ(n)

 It then follows that

 | Pr[t ← Xn : D ( M(t)) = 1] − Pr[t ← Yn : D ( M(t)) = 1]| > µ(n).

 In that case, the non-uniform p.p.t. machine D 0 (·) = D ( M(·))
 also distinguishes { Xn }n , {Yn }n with probability µ(n), which
 contradicts that the assumption that { Xn }n ≈ {Yn }n .        

 Transitivity - The Hybrid Lemma
 We next show that the notion of computational indistinguishabil-
 ity is transitive; namely, if { An }n ≈ { Bn }n and { Bn }n ≈ {Cn }n ,
 then { An }n ≈ {Cn }n . In fact, we prove a generalization of this
 statement which considers m = poly(n) distributions.

.Lemma 71.6 (Hybrid Lemma) Let X 1 , X 2 , . . . , X m be a sequence of
 probability distributions. Assume that the machine D distinguishes X 1
 72          chapter 3. indistinguishability & pseudo-randomness


 and X m with probability e. Then there exists some i ∈ [1, . . . , m − 1]
 s.t. D distinguishes X i and X i+1 with probability me .

 Proof. Assume D distinguishes X 1 , X m with probability e. That
 is,
          h                 i
      | Pr t ← X : D (t) = 1 − Pr [t ← X m : D (t) = 1] | > e
                1



 Let gi = Pr t ← X i : D (t) = 1 . Thus, | g1 − gm | > e. This im-
                               

 plies,

             | g1 − g2 | + | g2 − g3 | + · · · + | g m − 1 − g m |
                 ≥ | g1 − g2 + g2 − g3 + · · · + g m − 1 − g m |
                 = | g1 − gm | > e.

 Therefore, there must exist i such that | gi − gi+1 | > me .          

.Remark 72.7 (A geometric interpretation) Note that the probabil-
 ity with which D outputs 1 induces a metric space over probability
 distributions over strings t. Given this view the hybrid lemma is just a
 restatement of the triangle inequality over this metric spaces; in other
 words, if the distance between two consecutive probability distributions
 is small, then the distance between the extremal distributions is also
 small.

 Note that because we lose a factor of m when we have a sequence
 of m distributions, the hybrid lemma can only be used to deduce
 transitivity when m is polynomially-related to the security pa-
 rameter n. (In fact, it is easy to construct a “long” sequence of
 probability distributions in which each adjacent pair of distribu-
 tions are indistinguishable, but where the extremal distributions
 are distinguishable.)

 Example
 Let { Xn }n , {Yn }n and { Zn }n be pairwise indistinguishable prob-
 ability ensembles, where Xn , Yn , and Zn are distributions over
 {0, 1}n . Assume further that we can efficiently sample from
 all three ensembles. Consider the n.u. p.p.t. machine M(t)
 that samples y ← Yn where n = |t| and outputs t ⊕ y. Since
 3.1. Computational Indistinguishability                                73


 { Xn }n ≈c { Zn }n , closure under efficient operations directly im-
 plies that

     { x ← Xn ; y ← Yn : x ⊕ y}n ≈c {y ← Yn ; z ← Zn : z ⊕ y}n


 Distinguishing versus Predicting

 The notion of computational indistinguishability requires that
 no efficient distinguisher can tell apart two distributions with
 more than a negligible advantage. As a consequence of this
 property, no efficient machine can predict which distribution a
 sample comes from with probability 12 + poly1(n) ; any such predic-
 tor would be a valid distinguisher (show this!). As the following
 useful lemma shows, the converse also holds: if it is not possible
 to predict which distribution a sample comes from with proba-
 bility significantly better than 12 , then the distributions must be
 indistinguishable.

.Lemma 73.8 (The Prediction Lemma) Let { Xn0 }n and { Xn1 }n be
 two ensembles where Xn0 and Xn1 are probability distributions over
 {0, 1}`(n) for some polynomial `(·), and let D be a n.u. p.p.t. machine
 that distinguishes between { Xn0 }n and { Xn1 }n with probability µ(·) for
 infinitely many n ∈ N. Then there exists a n.u. p.p.t. A such that

             h                              i 1 µ(n)
           Pr b ← {0, 1}; t ← Xnb : A(t) = b ≥ +     .
                                              2  2

 for infinitely many n ∈ N.

 Proof. Assume without loss of generality that D outputs 1 with
 higher probability when receiving a sample from Xn1 than when
 receiving a sample from Xn0 , i.e.,

    Pr[t ← Xn1 : D (t) = 1] − Pr[t ← Xn0 : D (t) = 1] > µ(n)        (73.2)

 This is without loss of generality since otherwise, D can be
 replaced with D 0 (·) = 1 − D (·); one of these distinguishers
 works for infinitely many n ∈ N. We show that D is also a
 74         chapter 3. indistinguishability & pseudo-randomness


“predictor”:
    h                               i
 Pr b ← {0, 1}; t ← Xnb : D (t) = b
      1 h                      i                         
         Pr t ← Xn1 : D (t) = 1 + Pr t ← Xn0 : D (t) 6= 1
                                        
   =
      2
      1 h                      i                            
         Pr t ← Xn1 : D (t) = 1 + 1 − Pr t ← Xn0 : D (t) = 1
                                          
   =
      2
      1 1 h                          i                      
             Pr t ← Xn1 : D (t) = 1 − Pr t ← Xn0 : D (t) = 1
                                           
   = +
      2 2
         1 µ(n)
   = > +
         2     2
                                                                   


 3.2 Pseudo-randomness
 Using the notion of computational indistinguishability, we next
 turn to defining pseudo-random distributions.

 3.2.1 Definition of Pseudo-random Distributions
 Let Un denote the uniform distribution over {0, 1}n , i.e, Un =
 {t ← {0, 1}n : t}. We say that a distribution is pseudo-random if
 it is indistinguishable from the uniform distribution.

.Definition 74.1 (Pseudo-random Ensembles). The probability
 ensemble { Xn }n , where Xn is a probability distribution over
 {0, 1}l (n) for some polynomial l (·), is said to be pseudorandom if
 { Xn }n ≈ {Ul (n) }n .

     Note that this definition effectively says that a pseudorandom
 distribution needs to pass all efficiently computable statistical
 tests that the uniform distribution would have passesd; otherwise
 the statistical test would distinguish the distributions.
     Thus, at first sight it might seem very hard to check or prove
 that a distribution is pseudorandom. As it turns out, there
 are complete statistical tests; such a test has the property that
 if a distribution passes only that test, it will also pass all other
 efficient tests. We proceed to present such a test.
 3.2. Pseudo-randomness                                                     75


 3.2.2    A complete statistical test: The next-bit test
 We say that a distribution passes the next-bit test if no efficient
 adversary can, given any prefix of a sequence sampled from the
 distribution, predict the next bit in the sequence with probability
 significantely better than 12 (recall that this was one of the test
 originally suggested in the introduction of this chapter).

.Definition 75.2 An ensemble { Xn }n where Xn is a probability dis-
 tribution over {0, 1}`(n) for some polynomial l (n) is said to pass the
 Next-Bit Test if for every non-uniform p.p.t. A, there exists a negligible
 function e(n) such that ∀n ∈ N and ∀i ∈ [0, · · · , `(n)], it holds that

                                                             1
           Pr [t ← Xn : A(1n , t1 t2 . . . ti ) = ti+1 ] <     + e ( n ).
                                                             2
 Here, ti denotes the i’th bit of t.

.Remark 75.3 Note that we provide A with the additional input 1n .
 This is simply allow A to have size and running-time that is polynomial
 in n and not simply in the (potentially) short prefix t0 . . . ti .

.Theorem 75.4 (Completeness of the Next-Bit Test) If a probabil-
 ity ensemble { Xn }n passes the next-bit test then { Xn }n is pseudo-
 random.

 Proof. Assume for the sake of contradiction that there exists a
 non-uniform p.p.t. distinguisher D, and a polynomial p(·) such
 that for infinitely many n ∈ N, D distinguishes Xn and U`(n)
 with probability p(1n) . We contruct a machine A that predicts
 the next bit of Xn for every such n. Define a sequence of hybrid
 distributions as follows.
            n                                                        o
     Hni = x ← Xn : u ← U`(n) : x0 x1 . . . xi ui+1 ui+2 . . . u`(n)

                                       `(n)
 Note that Hn0 = U`(n) and Hn
                           = Xn . Thus, D distinguishes
                 `(n)
 between Hn and Hn with probability p(1n) . It follows from
          0

 the hybrid lemma that there exists some i ∈ [0, `(n)] such that
 D distinguishes between Hni and Hni+1 with probability p(n)`(
                                                            1
                                                               n)
                                                                  .
 Recall, that the only difference between H i+1 and H i is that in
76           chapter 3. indistinguishability & pseudo-randomness


H i+1 the (i + 1)th bit is xi+1 , whereas in H i it is ui+1 . Thus,
intuitively, D—given only the prefix x1 . . . xi —can tell apart xi+1
from a uniformly chosen bit. This in turn means that D also can
tell apart xi+1 from x̄i+1 . More formally, consider the distribution
H̃ni defined as follows:
           n                                                            o
     H̃ni = x ← Xn : u ← U`(n) : x0 x1 . . . xi−1 x̄i ui+1 . . . ul (m)

Note that Hni can be sampled by drawing from Hni+1 with proba-
bility 1/2 and drawing from H̃ni+1 with probability 1/2. Substi-
tuting this identity into the last of term
         h                       i       h               i
      Pr t ← Hni+1 : D (t) = 1 − Pr t ← Hni : D (t) = 1

yields

   Pr t ← Hni+1 : D (t) = 1 −
                               
       1          i +1 : D ( t ) = 1] + 1 Pr[ t ← H̃ i +1 : D ( t ) = 1]
                                                                         
       2 Pr[ t ← Hn                     2           n

which simplifies to
     1   h                     i    h                       i
       Pr t ← Hni+1 : D (t) = 1 − Pr t ← H̃ni+1 : D (t) = 1
     2
Combining this equation with the observation above that D
distinguishes Hni and Hni+1 with probability p(n)`(
                                                1
                                                    n)
                                                       implies that
D distinguishes Hni+1 and H̃ni+1 with probability p(n)`(
                                                     2
                                                         n)
                                                            . By the
prediction lemma, there must therefore exist a machine A such
that
       h                                   i  1          1
     Pr b ← {0, 1}; t ← Hni+1,b : D (t) = b > +
                                              2    p(n)`(n)

where we let Hni+1,1 denote Hni+1 and Hni+1,0 denote H̃ni+1 . (i.e., A
predicts whether a sample came from Hni+1 or H̃ni+1 .) We can now
use A to construct a machine A0 predicts xi+1 (i.e., the (i + 1)th
bit in the pseudorandom sequence):
algorithm 76.5: A0 (1n , t1 , . . . , ti ): A next-bit predictor
  Pick `(n) − i random bits ui+1 . . . u`(n) ← U `(n)−1
  Run g ← A(t1 . . . ti ui+1 . . . u`(n) )
 3.3. Pseudo-random generators                                        77


   if g = 1 then
      Output ui+1
   else
      Output ūi+1 = 1 − ui+1
   end if
 Note that,

  Pr t ← Xn : A0 (1n , t1 . . . ti ) = ti+1
                                           
            h                                 i 1    1
     = Pr b ← {0, 1}; t ← Hni+1,b : A(t) = 1 > +
                                                2 p(n)`(n)

 which concludes the proof Theorem 75.4.                              


 3.3 Pseudo-random generators
 We now turn to definitions and constructions of pseudo-random
 generators.

 3.3.1   Definition of a Pseudo-random Generators
.Definition 77.1 (Pseudo-random Generator). A function G :
 {0, 1}∗ → {0, 1}∗ is a Pseudo-random Generator (PRG) if the fol-
 lowing holds.

   1. (efficiency): G can be computed in p.p.t.
   2. (expansion): | G ( x )| > | x |
   3. The ensemble { x ← Un : G ( x )}n is pseudo-random.

 3.3.2   An Initial Construction
 To provide some intuition for our construction, we start by con-
 sidering a simplified construction (originally suggested by Adi
 Shamir). The basic idea is to iterate a one-way permutation and
 then output, in reverse order, all the intermediary values. More
 precisely, let f be a one-way permutation, and define the genera-
 tor G (s) = f n (s) k f n−1 (s) k . . . k f (s) k s. We use the k symbol
 here to represent string concatentation.
     The idea behind the scheme is that given some prefix of the
 output of the generator, computing the next block is equivalent
 78         chapter 3. indistinguishability & pseudo-randomness


  G(s) =      f n (s)   f n−1 (s) f n−2 (s)   ...   f (s)     s



               Figure 78.2: Shamir’s proposed PRG


 to inverting the one-way permutation f . Indeed, this scheme
 results in a sequence of unpredictable numbers, but not necessarily
 unpredictable bits. In particular, a one-way permutation may
 never “change” the first two bits of its input, and thus those
 corresponding positions will always be predictable.
     The reason we need f to be a permutation, and not a gen-
 eral one-way function, is two-fold. First, we need the domain
 and range to be the same number of bits. Second, and more
 importantly, we require that the output of f k ( x ) be uniformly
 distributed if x is uniformly distributed. This holds if f is a
 permutation, but may not hold for a general one-way function.
     As we shall see, this construction can be modified to generate
 unpredictable bits as well. Doing so requires the new concept of
 a hard-core bit.

 3.3.3 Hard-core bits
 Intuitively, a predicate h is hard-core for a OWF f if h( x ) cannot
 be predicted significantly better than with probability 1/2, even
 given f ( x ). In other words, although a OWF might leak many
 bits of its inverse, it does not leak the hard-core bits—in fact, it
 essentially does not leak anything about the hard-core bits. Thus,
 hard-core bits are computationally unpredictable.

.Definition 78.3 (Hard-core Predicate). A predicate h : {0, 1}∗ →
 {0, 1} is a hard-core predicate for f ( x ) if h is efficiently com-
 putable given x, and for all nonuniform p.p.t. adversaries A,
 there exists a negligible e so that ∀k ∈ N
           h                                      i 1
         Pr x ← {0, 1}k : A(1n , f ( x )) = h( x ) ≤ + e(n)
                                                    2

 Examples The least significant bit of the RSA one-way function
 is known to be hardcore (under the RSA assumption). That
 3.3. Pseudo-random generators                                     79


 is, given N, e, and f RSA ( x ) = x e mod N, there is no efficient
 algorithm that predicts LSB( x ). A few other examples include:

    • The function half N ( x ) which is equal to 1 iff 0 ≤ x ≤ N2 is
      also hardcore for RSA, under the RSA assumption.

    • The function half p−1 ( x ) is a hardcore predicate for expo-
      nentiation to the power x mod p for a prime p under the
      DL assumption. (See §3.4.1 for this proof.)

     We now show how hard-core predicates can be used to con-
 struct a PRG.


 3.3.4   Constructions of a PRG
 Our idea for constructing a pseudo-random generator builds on
 Shamir’s construction above that outputs unpredictable numbers.
 Instead of outputting all intermediary numbers, however, we only
 output a “hard-core” bit of each of them. We start by providing
 a construction of a PRG that only expands the seed by one bit,
 and then give the full construction in Corollary 81.7.


.Theorem 79.4 Let f be a one-way permutation, and h a hard-core
 predicate for f . Then G (s) = f (s) k h(s) is a PRG.


 Proof. Assume for contradiction that there exists a nonuniform
 p.p.t. adversary A and a polynomial p(n) such that for infinitely
 many n, there exists an i such that A predicts the ith bit with
 probability p(1n) . Since the first n bits of G (s) are a permutation
 of a uniform distribution (and thus also uniformly distributed),
 A must predict bit n + 1 with advantage p(1n) . Formally,

                                            1    1
                  Pr[ A( f (s)) = h(s)] >     +
                                            2   p(n)

 This contradicts the assumption that b is hard-core for f . We
 conclude that G is a PRG.                                    
 80         chapter 3. indistinguishability & pseudo-randomness


 3.3.5   Expansion of a PRG
 The construction above from Thm. 79.4 only extends an n-bit
 seed to n + 1 output bits. The following theorem shows how a
 PRG that extends the seed by only 1 bit can be used to create a
 PRG that extends an n-bit seed to poly(n) output bits.

.Lemma 80.5 Let G : {0, 1}n → {0, 1}n+1 be a PRG. For any polyno-
 mial `, define G 0 : {0, 1}n → {0, 1}`(n) as follows (see Fig. 6):

                             G 0 (s) = b1 . . . b`(n) where
                                 X0 ← s
                      X i + 1 k bi + 1 ← G ( X i )

 Then G 0 is a PRG.


                                       s
                                     G(s)
                                      X0        b0
                                    G(X0 )

                                     X1        b1
                                    G(X1 )
                                     X2        b2

 Figure 80.6: Illustration of the PRG G 0 that expands a seed of
 length n to `(n). The function G is a PRG that expands by only 1
 bit.

 Proof. Consider the following recursive definition of G 0 (s) =
 G m ( s ):

             G0 ( x ) = ε
              Gi ( x ) = b|| Gi−1 ( x 0 ) where x 0 ||b ← G ( x )
 3.3. Pseudo-random generators                                                      81


 where ε denotes the empty string. Now, assume for contradic-
 tion that there exists a distinguisher D and a polynomial p(·)
 such that for infinitely many n, D distinguishes {Um(n) }n and
 { G 0 (Un )}n with probability p(1n) .
    Define the hybrid distributions Hni = Um(n)−i || Gi (Un ), for
                                                               m(n)
 i = 1, . . . , m(n). Note that Hn0 = Um(n) and Hn                    = G m(n) (Un ).
                                m(n)
 Thus, D distinguishes Hn0 and Hn    with probability p(1n) .      By
 the Hybrid Lemma, for each n, there exist some i such that D
 distinguishes Hni and Hni+1 with probability m(n)1p(n) . Recall that,

              Hni = Um−i k Gi (Un )
                   = Um−i−1 kU1 k Gi (Un )
             Hni+1 = Um−i−1 k Gi+1 (Un )
                   = Um−i−1 kbk Gi ( x ) where x kb ← G (Un )

  Consider the n.u. p.p.t. M(y) which outputs from the following
 experiment:
                      b prev ← Um−i−1
                      b ← y1
                      bnext ← Gi (y2 . . . yn+1 )
                      Output b prev kbkbnext
 Algorithm M (y) is non-uniform because for each input length n,
 it needs to know the appropriate i. Note that M (Un+1 ) = Hni and
 M ( G (Un )) = Hni+1 . Since (by the PRG property of G) {Un+1 }n ≈
 { G (Un )}n , it follows by closure under efficient operations that
 { Hni }n ≈ { Hni+1 }n , which is a contradiction.                
      By combining Theorem 79.4 and Lemma 80.5, we get the final
 construction of a PRG.

.Corollary 81.7 Let f be a OWP and h a hard core bit for f . Then

      G ( x ) = h( x ) k h( f ( x )) k h( f (2) ( x )) k . . . k h( f `(n) ( x ))

 is a PRG.

 Proof. Let G 0 ( x ) = f ( x ) k h( x ). By Theorem 79.4 G 0 is a PRG.
 Applying Lemma 80.5 to G 0 shows that G also is a PRG. See
 Fig. 8.                                                             
82           chapter 3. indistinguishability & pseudo-randomness


              s                     f (s)               f (2) ( s )            ...

                  h(s)                  h( f (s))              h( f (2) (s))
              b0                     b1                    b2


Figure 82.8: Illustration of a PRG based on a one-way permuta-
tion f and its hard-core bit h.

    Note that the above PRG can be computed in an “on-line”
fashion. Namely, we only need to remember xi to compute the
continuation of the output. This makes it possible to compute
an arbitrary long pseudo-random sequence using only a short
seed of a fixed length. (In other words, we do not need to know
an upper-bound on the length of the output when starting to
generate the pseudo-random sequence.)
    Furthermore, note that the PRG construction can be easily
adapted to work also with a collection of OWP, and not just a
OWP. If { f i } is a collection of OWP, simply consider G defined
as follows:
                                                         (2)
                  G (r1 , r2 ) = hi ( f i ( x )) k hi ( f i ( x )) k . . .

where r1 is used to sample i and r2 is used to sample x.

3.3.6 Concrete examples of PRGs
By using our concrete candidates of OWP (and their correspond-
ing hard-core bits), we get the following concrete instantiations
of PRGs.

Modular Exponentiation                 (Blum-Micali PRG)

     • Use the seed to generate p, g, x where p is a prime of the
       form 2q + 1 and q is also prime, g is a generator for Z∗p ,
       and x ∈ Z∗p .
                                                                                     x
     • Output half p−1 ( x ) k half p−1 ( g x mod p) k half p−1 ( g g mod
       p) k · · ·
3.4. Hard-Core Bits from Any OWF                                  83


RSA (RSA PRG)

   • Use the seed to generate p, q, e where p, q are random n-
     bit primes p, q, and e is a random element in Z∗N where
     N = pq.

   • Output LSB( x ) k LSB( x e mod N ) k LSB(( x e )e mod N ) k
     · · · where LSB( x ) is the least significant bit of x.

Rabin   (Blum-Blum-Schub)

   • Use seed to generate random k-bit primes p, q = 3 mod 4
     and x ∈ QRn , where n = pq.

   • Output LSB( x ) k LSB( x2 mod N ) k LSB(( x2 )2 mod N ) k
     . . . where LSB( x ) is the least significant bit of x.

   • This is efficient: given the state xi , only one modular multi-
     plication is needed to get the next bit. C.f. linear congruen-
     tial generators G ( xi+1 ) = axi + b.

   • We can efficiently compute the ith bit (i.e., LSB( x2 )i ) with-
     out needing to keep state ( x2 )i−1 , provided that the primes
     p and q are known. This is because we can easily compute
     Φ( pq).

In all the above PRGs, we can in fact output log n bits at each
iteration, while still remaining provably secure. Moreover, it is
conjectured that it is possible to output n2 bits at each iteration
and still remain secure (but this has not been proven).


3.4 Hard-Core Bits from Any OWF
We have previously shown that if f is a one-way permutation
and h is a hard-core predicate for f , then the function

                        G (s) = f (s) k h(s)

is a pseudo-random generator. One issue, however, is how to find
a hard-core predicate for a given one-way permutation. We have
illustrated examples for some of the well-known permutations.
 84            chapter 3. indistinguishability & pseudo-randomness


 Here, we show that every one-way function (permutation resp.)
 can be transformed into another one-way function (permutation
 resp.) which has a hard-core bit. Combined with our previous
 results, this shows that a PRG can be constructed from any one-
 way permutation.
     As a warm-up, we show that half p−1 is a hardcore predicate
 for exponentiation mod p (assuming the DL assumption).

 3.4.1 A Hard-core Bit from the Discrete Log problem
 Recall that halfn ( x ) is equal to 1 if and only iff 0 ≤ x ≤ n2 .

.Lemma 84.1 Under the DL assumption (52.2), the function half p−1
 is a hard-core predicate for the exponentiation function f p,g ( x ) = g x
 mod p from the discrete-log collection DL.

 Proof. First, note that it is easy to compute half p−1 () given x.
 Suppose, for the sake of contradiction, that there exists a n.u.
 p.p.t. algorithm A and a polynomial s(n) such that for infinitely
 many n ∈ N
         h                                                              i
     Pr f p,g ← DL(n); x ← Z p : A(1n , f p,g ( x )) = half( p−1) ( x )
               1   1
           >     +
               2 s(n)

 We show how to use the algorithm A to construct a new algo-
 rithm B which solves the discrete logarithm problem for the same
 n and therefore violates the discrete log assumption. To illustrate
 the idea, let us first assume that A is always correct. Later we
 remove this assumption. The algorithm B works as follows:
 algorithm 84.2: DiscreteLog( g, p, y) using A
  1: Set yk ← y and k = | p |
  2: while k > 0 do
  3:    if yk is a square mod p then
  4:       xk ← 0
  5:    else
  6:       xk ← 1
  7:       yk ← yk /g mod p to make a square
  8:    end if
3.4. Hard-Core Bits from Any OWF                                      85

                                             √
 9:   Compute the square root yk−1 ←             yk mod p
10:   Run b ← A(yk−1 )
11:   IF b = 0 THen yk−1 ← −yk−1
12:   Decrement k
13: end while
14: return x

      Recall from Thm. 58.2 and the related exercises on that page,
for every prime p, the modular square root operation can be
performed efficiently.
      Now if g is a generator, and y is square y = g2x , notice
that y has two square roots: g x and g x+ p/2 . (Recall that g p/2 =
−1 mod p.) The first of these two roots has a smaller discrete
log than y, and the other has a larger one. If it is possible to
determine which of the two roots is the smaller root—say by
using the adversary A to determine whether the exponent of the
root is in the “top half” [1, p/2] or not—then we can iteratively
divide, take square-roots, and then choose the root with smaller
discrete log until we eventually end up at 1. This is in fact the
procedure given above.
      Unfortunately, we are not guaranteed that A always outputs
the correct answer, but only that A is correct noticably more often
than not. In particular, A is correct with probability 12 + e where
e = s(n). To get around this problem, we can use self-reducibility
in the group Z p . In particular, we can choose ` random values
r1 , . . . , r` , and randomize the values that we feed to A in line 8 of
Alg. 84.2. Since A must be noticably more correct than incorrect,
we can use a “majority vote” to get an answer that is correct with
high probability.
      To formalize this intuition, we first demonstrate that the
procedure above can be used to solve the discrete log for instances
in which the discrete log is in the range [1, 2, . . . , e/4 · p]. As we
will show later, such an algorithm suffices to solve the discrete
log problem, since we can guess and map any instance into this
range. Consider the following alternative test in place of line 8
of Alg. 84.2.
    lo ← 0
    for i = 1, 2, . . . , ` do
        ri ← Z p
86          chapter 3. indistinguishability & pseudo-randomness


     z i ← y k −1 g r i
     bi ← A ( z i )
     Increment lo if (bi = 0 ∧ ri < p/2) or (bi = 1 ∧ ri ≥ p/2)
  end for
  Set b = 0 if lo > `/2 and 1 otherwise
Suppose the discrete log of yk is in the range [1, 2, . . . , s] where
s = e/4 · p. It follows that either the discrete log of yk−1 falls
within the range [1, 2, . . . , s/2] or in the range [ p/2, . . . p/2 + s/2].
In other words, the square root will either be slightly greater
than 0, or slightly greater than p/2. Let the event noinc represent
the case when the counter lo is not incremented in line 13. By
the Union Bound, we have that

Pr [noinc | low(yk−1 )] ≤ Pr[ A(zi ) errs]
                            + Pr[ri ∈ [ p/2 − s, p/2] ∪ [ p − s, p − 1]]

The last term on the right hand side arises from the error of re-
randomizing. That is, when ri ∈ [ p/2 − s, p/2], then the discrete
log of zi will be greater than p/2. Therefore, even if A answers
correctly, the test on line 13 will not increment the counter lo.
Although this error in unavoidable, since ri is chosen randomly,
we have that
                                      1               1 e
         Pr[noinc | low(yk−1 )] ≤       − e + 2(e/4) = −
                                      2               2 2
Conversely, the probability that lo is incremented is therefore
greater than 1/2 + e/2. By setting the number of samples ` =
(1/e)2 , then by the corollary of the Chernoff bound given in
Lemma 189.8, value b will be correct correct with probability
very close to 1.
                                                                
    In the above proof, we rely on specific properties of the OWP
f . We proceed to show how the existence of OWPs implies the
exitence of OWPs with a hard-core bit.

3.4.2 A General Hard-core Predicate from Any OWF
Let h x, r i denote the inner product of x and r, i.e., ∑ xi ri mod 2.
In other words, r decides which bits of x to take parity on.
 3.4. Hard-Core Bits from Any OWF                                          87


.Theorem 87.3 Let f be a OWF (OWP) and define function g( x, r ) =
 ( f ( x ), r ) where | x | = |r |. Then g is a OWF (OWP) and h( x, r ) =
 h x, r i is a hardcore predicate for f .

 3.4.3    *Proof of Theorem 87.3
 Proof. We show that if A, given g( x, r ) can compute h( x, r ) with
 probability non-negligibly better than 1/2, then there exists a
 p.p.t. adversary B that inverts f . More precisely, we use A to
 construct a machine B that on input y = f ( x ) recovers x with
 non-negligible probability, which contradicts the one-wayness
 of f . The proof is fairly involved. To provide intuition, we first
 consider two simplified cases.

 Oversimplified case: assume A always computes h( x, r ) cor-
 rectly. (Note that this is oversimplified as we only know that
 A computes h( x, r ) with probability non-negligibly better than
 1/2.) In this case the following simple procedure recovers x: B
 on input y lets xi = A(y, ei ) where ei = 00..010.. is an n bit string
 with the only 1 being in position i, and outputs x1 , x2 , . . . , xn .
 This clearly works, since by definition h x, ei i = xi and by our
 assumption A( f ( x ), r ) = h x, r i.

 Less simplified case: assume A computes h( x, r ) with proba-
 bility 43 + e(n) where e(n) = poly1(n) . In this case, the above
 algorithm of simply querying A with y, ei no longer work for
 two reasons:

    1. A might not work for all y’s,

    2. even if A predicts h( x, r ) with high probabiliy for a given
       y, but a random r, it might still fail on the particular r = ei .

 To get around the first problem, we show that for a reasonable
 fraction of x’s, A does work with high probability. We first define
 the “good set” of instances
                                                                      
                                n                                3 e
     S=       x | Pr [r ← {0, 1} : A( f ( x ), r ) = h( x, r )] > +
                                                                 4 2
 88           chapter 3. indistinguishability & pseudo-randomness


 Let us first argue that Pr [ x ∈ S] ≥ 2e . Suppose, for the sake of
 contradiction, that it is not. Then we have

          Pr [ x, r ← {0, 1}n : A( f ( x ), r ) = h( x, r )]
             ≤ (Pr [ x ∈ S] · 1)
               + (Pr [ x ∈
                         / S] · Pr [A( f ( x ), r ) = h( x, r )| x ∈
                                                                   / S])
               e                   
                                          3 e
                                                   
             <       + (1 − e/2) ·           +
                 2                        4 2
               3
             < +e
               4
which contradicts our assumption. The second term on the third
line of the derivation follows because by definition of S, when
x 6∈ S, then A succeeds with probability less than 34 + e/2.
    The second problem is more subtle. To get around it, we
“obfuscate” the queries y, ei and rely on the linearity of the inner
product operation. The following simple fact is useful.

.Fact 88.4 h a, b ⊕ ci = h a, bi ⊕ h a, ci mod 2
 Proof.

                h a, b ⊕ ci = Σai (bi + ci ) = Σai bi + Σai ci
                            = h a, bi + h a, ci mod 2

                                                                      
     Now, rather than asking A to recover h x, ei i, we instead pick
 a random string r and ask A to recover h x, r i and h x, r + e1 i, and
 compute the XOR of the answers. If A correctly answers both
 queries, then the i’th bit of x can be recovered. More precisely,
 B(y) proceeds as follows:
 algorithm 88.5: B(y)
   m ← poly(1/e)
   for i = 1, 2, . . . , n do
     for j = 1, 2, . . . , m do
        Pick random r ← {0, 1}n
        Set r 0 ← ei ⊕ r
        Compute a guess gi,j for xi as A(y, r ) ⊕ A(y, r 0 )
     end for
3.4. Hard-Core Bits from Any OWF                                      89


    xi ← majority( gi,1 , . . . , gi,m )
  end for
  Output x1 , . . . , xn .

Note that for a “good” x (i.e., x ∈ S) it holds that:

   • with probability at most 14 − 2e , A(y, r ) 6= h( x, r )

   • with probability at most 14 − 2e , A(y, r 0 ) 6= h( x, r )

It follows by the union bound that with probability at least 12 + e
both answers of A are correct. Since hy, r i ⊕ hy, r 0 i = hy, r ⊕ r 0 i =
hy, ei i, each guess gi is correct with probability 12 + e. Since
algorithm B attempts poly(1/e) independent guesses and finally
take a majority vote, it follows using the Chernoff Bound that
every bit is xi computed by B is correct with high probability.
Thus, for a non-negligible fraction of x’s, B inverts f , which is a
contradiction.

The general case. We proceed to the most general case. Here,
we simply assume that A, given random y = f ( x ) and random r
computes h( x, r ) with probability 12 + e (where e = poly1(n) ). As
before, define the set of good cases as
                                                        
                                                     1 e
           S = x | Pr [A( f ( x ), r ) = h( x, r )] > +
                                                     2 2

It again follows that Pr [ x ∈ S] ≥ 2e . To construct B , let us first as-
sume that B can call a subroutine C that on input f ( x ), produces
samples
              (b1 = h x, r1 i, r1 ), . . . , (bm = h x, rm i, rm )
where r1 , . . . , rm are independent and random. Consider the
following procedure B(y):
algorithm 89.6: B(y) for the General case
  m ← poly(1/e)
  for i = 1, 2, . . . , n do
    (b1 , r1 ), . . . , (bm , rm ) ← C (y)
    for j = 1, 2, . . . , m do
       Let r 0j = ei ⊕ r j
90           chapter 3. indistinguishability & pseudo-randomness


      Compute gi,j = b j ⊕ A(y, r 0 )
    end for
    Let xi ← majority( g1 , . . . , gm )
  end for
  Output x1 , . . . , xn .
      Given an x ∈ S, it follows that each guess gi,j is correct with
probability 12 + 2e = 12 + e0 . We can now again apply the the
Chernoff bound to show that xi is wrong with probability ≤
      02
2−e m . Thus, as long as m >> e102 , we can recover all xi . The only
problem is that B uses the magical subroutine C.
      Thus, it remains to show how C can be implemented. As
an intermediate step, suppose that C were to produce samples
(b1 , r1 ), . . . , (bn , rn ) that were only pairwise independent (instead
of being completely independent). It follows by the Pairwise-
Independent Sampling inequality that each xi is wrong with
                                 −4e02
probability at most 14me                       1
                                    02 ≤ me02 . By union bound, any of the
xi is wrong with probability at most n/me02 which is less than 1/2
when m ≥ e2n02 . Thus, if we could get 2n/e02 pairwise independent
samples, we would be done. So, where can we get them from?
A simple approach to generating these samples would be to pick
r1 , . . . , rm at random and guess b1 , . . . , bm randomly. However,
bi would be correct only with probability 2−m . A better idea
is to pick log(m) samples s1 , . . . , slog(m) and guess b10 , . . . , blog
                                                                         0
                                                                            (m) ;
here the guess is correct with probability 1/m. Now, gener-
ate r1 , r2 , . . . , rm−1 as all possible sums (modulo 2) of subsets of
s1 , . . . , slog(m) , and b1 , b2 , . . . , bm as the corresponding subsets of
bi0 . That is,
                         ri = ∑ s j j ∈ I iff i j = 1
                               j∈ Ii

                        bi = ∑ b0j
                               j∈ Ii

       It is not hard to show that these ri are pairwise independent
samples (show this!). Yet with probability 1/m, all guesses for
b10 , . . . , blog
               0
                   (m) are correct, which means that b1 , . . . , bm−1 are also
correct.
       Thus, for a fraction of e0 of x 0 it holds that with probability
1/m, the algorithm B inverts f with probability 1/2. That is, B
 3.5. Secure Encryption                                             91


 inverts f with probability

                           e0   e 03   (e/2)3
                              =      =
                          2m    4n       4n

 when m = 2n
          e2
             . This contradicts the one-wayness of f .


 3.5 Secure Encryption
 We next use the notion of indistinguishability to provide a com-
 putational definition of security of encryption schemes. As we
 shall see, the notion of a PRG will be instrumental in the con-
 struction of encryption schemes which permit the use of a short
 key to encrypt a long message.
     The intuition behind the definition of secure encryption is
 simple: instead of requiring that encryptions of any two messages
 are identically distributed (as in the definition of perfect secrecy),
 the computational notion of secure encryption requires only that
 encryptions of any two messages are indistinguishable.


.Definition 91.1 (Secure Encryption). The encryption scheme
 (Gen, Enc, Dec) is said to be single-message secure if ∀ non uniform
 p.p.t. D, there exists a negligible function e(·) such that for
 all n ∈ N, m0 , m1 ∈ {0, 1}n , D distinguishes between the the
 following distributions with probability at most e(n):

    • {k ← Gen(1n ) : Enck (m0 )}
    • {k ← Gen(1n ) : Enck (m1 )}


     The above definition is based on the indistinguishability of
 the distribution of ciphertexts created by encrypting two different
 messages. The above definition does not, however, explicitly cap-
 ture any a priori information that an adversary might have. Later
 in the course, we will see a definition which explicitly captures
 any a priori information that the adversary might have and in fact
 show that the indistinguishability definition is equivalent to it.
 92          chapter 3. indistinguishability & pseudo-randomness


 3.6 An Encryption Scheme with Short Keys
 Recall that perfectly secure encryption schemes require a key that
 is at least as long as the message to be encrypted. In this section
 we show how a short key can be used to construct a secure
 encryption scheme. The idea is to use a one-time pad encryption
 scheme in which the pad is the output of a pseudo-random
 generator (instead of being truly random). Since we know how
 to take a small seed and construct a long pseudorandom sequence
 using a PRG, we can encrypt long messages with a short key.
     More precisely, consider the following encryption scheme.
 Let G (s) be a length-doubling pseudo-random generator.
 algorithm 92.1: Encryption Scheme for n-bit message

  Gen(1n ): k ← Un/2
  Enck (m): Output m ⊕ G (k )
  Deck (c): Output c ⊕ G (k )


.Theorem 92.2 Scheme (Gen, Enc, Dec) described in Algorithm 92.1
 is single-message secure.

 Proof. Assume for contradiction that there exists a distinguisher
 D and a polynomial p(n) such that for infinitely many n, there
 exist messages m0n , m1n such that D distinguishes between the
 following two distributions

      • {k ← Gen(1n ) : Enck (m0 )}

      • {k ← Gen(1n ) : Enck (m1 )}

 with probability 1/p(n). Consider the following hybrid distribu-
 tions:

      • Hn1 (Encryption of m0n ): {s ← Gen(1n ) : m0n ⊕ G (s)}.

      • Hn2 (OTP with m1n ): {r ← Un : m0n ⊕ r }.

      • Hn3 (OTP with m1n ): {r ← Un : m1n ⊕ r }.

      • Hn4 (Encryption of m1n ): {s ← Gen(1n ) : m1n ⊕ G (s)}.
 3.7. Multi-message Secure Encryption                                            93


 By construction D distringuishes Hn1 and Hn4 with probability
 1/p(n) for infinitely many n. It follows by the hybrid lemma
 that D also distinguishes two consequetive hybrids with prob-
 ability 1/4p(n) (for infinitely many n). We show that this is a
 contradiction.
     • Consider the n.u. p.p.t. machine Mi ( x ) = mi| x| ⊕ x1 and
       the distribution Xn = {s ← U n2 : G (s)}. By definition,
       Hn1 = M0 ( Xn ), Hn4 = M1 ( Xn ) and Hn2 = M0 (Un ), Hn3 =
       M1 (Un ). But since { Xn }n ≈ {Un }n (by the PRG property
       of G) it follows by closure under efficient operations that
       { Hn1 }n ≈ { Hn2 }n and { Hn3 }n ≈ { Hn4 }n .
     • Additionally, by the perfect secrecy of the OTP, Hn2 and Hn3
       are identically distributed.
 Thus, all consequetive hybrid distributions are indistinguishable,
 which is a contradiction.                                      

 3.7 Multi-message Secure Encryption
 As suggested by the name, single-message secure encryption only
 considers the security of an encryption scheme that is used to
 encrypt a single message. In general, we encrypt many messages
 and still require that the adversary cannot learn anything about
 the messages.
     The following definition extends single-message security to
 multi-message security. The definition is identical, with the only
 exception being that we require that the encryptions of any two
 vectors or messages are indistinguishable.

.Definition 93.1 (Multi-message Secure Encryption). An encryp-
 tion scheme (Gen, Enc, Dec) is said to be multi-message secure if
 for all non uniform p.p.t. D, for all polynomials q(n), there
 exists a negligible function e(·) such that for all n ∈ N and
 m0 , m1 , . . . , mq(n) , m00 , m10 , . . . , m0q(n) ∈ {0, 1}n , D distinguishes be-
 tween the the following distributions with probability at most
 e ( n ):
     1 Note that Mi is non-uniform as for each input lenght n, it has the message

 min hard-coded.
 94            chapter 3. indistinguishability & pseudo-randomness


      • {k ← Gen(1n ) : Enck (m0 ), Enck (m1 ), . . . Enck (mq(n) )}
      • {k ← Gen(1n ) : Enck (m00 ), Enck (m10 ), . . . Enck (m0q(n) )}

    It is easy to see that the single-message secure encryption
 scheme in Scheme 92.1 (i.e., Enck (m) = m ⊕ G (s), where G is a
 PRG) is not multi-message secure. More generally,

.Theorem 94.2 A multi-message secure encryption scheme cannot be
 deterministic and stateless.

 Proof. For any two messages m0 , m1 , consider the encryptions
 (c0 , c1 ), (c00 , c10 ) of the messages (m0 , m0 ) and (m0 , m1 ). If the
 encryption scheme is deterministic and stateless, c0 = c1 , but
 c00 6= c1 .                                                             
      Thus, any multi-message secure encryption scheme (that is
 stateless) must use randomness. One idea for such a scheme
 is to pick a random string r, then output r ||m ⊕ f (r ) for some
 function f . Ideally, we would like the output of f to be a random
 string as well. One way to get such an f might be to have a long
 pseudorandom sequence of length on the order of n2n . Then
 f could use r as an index into this sequence and return the
 n bits at r. But no pseudorandom generator can produce an
 exponential number of bits; the construction in §3.2 only works
 for pseudorandom generators with polynomial expansion.
      If we were to use a pseudorandom generator, then r could be
 at most O(log n) bits long, so even if r is chosen randomly, we
 would end up choosing two identical values of r with reasonable
 probability; this scheme would not be multi-message secure,
 though a stateful scheme that keeps track of the values of r
 used could be. What we need instead is a new type of “pseudo-
 random” function that allows us to index an exponentially long
 pseudo-random string.


 3.8 Pseudorandom Functions
 Before defining pseudorandom function, we first recall the defi-
 nition of a random function.
3.8. Pseudorandom Functions                                        95


3.8.1    Random Functions
The scheme r ||m ⊕ f (r ) would be multi-message secure if f were
a random function. We can describe a random functions in
two different ways: a combinatorial description—as a random
function table—and compuational description—as a machine
that randomly chooses outputs given inputs and keeps track
of its previous answers. In the combinatorial description, the
random function table can be view as a long array that stores the
values of f . So, f ( x ) returns the value at position nx.

        n bits     n bits       n bits                 n bits


     0101 . . .   1101 . . .   0010 . . .             0100 . . .

          1           2            3                     2n

Note that the description length of a random function is n2n ,
                 n
so there are 2n2 random functions from {0, 1}n → {0, 1}n . Let
RFn be the distribution that picks a function mapping {0, 1}n →
{0, 1}n uniformly at random.
     A computational description of a random function is instead
as follows: a random function is a machine that upon receiving
input x proceeds as follows. If it has not seen x before, it chooses
a value y ← {0, 1}n and returns y; it then records that f ( x ) = y.
If it has seen x before, then it looks up x, and outputs the same
value as before.

                     x
                                       f (x) = y
                     y


It can be seen that both of the above descriptions of a random
functions give rise to identical distributions.
    The problem with random functions is that (by definition)
they have a long description length. So, we cannot employ a
random function in our encryption scheme. We will next define
a pseudorandom function, which mimics a random function, but
has a short description.
 96           chapter 3. indistinguishability & pseudo-randomness


 3.8.2    Definition of Pseudorandom Functions
 Intuitively, a pseudorandom function (PRF) “looks” like a ran-
 dom function to any n.u. p.p.t. adversary. In defining this notion,
 we consider an adversary that gets oracle access to either the PRF,
 or a truly random function, and is supposed to decide which
 one it is interacting with. More precisely, an oracle Turing ma-
 chine M is a Turing machine that has been augmented with a
 component called an oracle: the oracle receives requests from M
 on a special tape and writes its responses to a tape in M. We
 now extend the notion of indistinguishability of distributions, to
 indistinguishability of distributions of oracles.

.Definition 96.1 (Oracle Indistinguishability). Let {On }n∈N and
 {On0 }n be ensembles where On , On0 are probability distributions
 over functions f : {0, 1}`1 (n) → {0, 1}`2 (n) for some polynomi-
 als `1 (·), `2 (·). We say that {On }n and {On0 }n are computation-
 ally indistinguishable (denoted by {On0 }n ≈ {On0 }n∈N ) if for all
 non-uniform p.p.t. oracles machines D, there exists a negligible
 function e(·) such that ∀n ∈ N
                    h                         i
                 Pr F ← On : D F(·) (1n ) = 1
                       h                           i < e ( n ).
                   − Pr F ← On0 : D F(·) (1n ) = 1

 It is easy to verify that oracle indistinguishability satisfies “clo-
 sure under efficient operations”, the Hybrid Lemma, and the
 Prediction Lemma.
      We turn to define pseudorandom functions.

.Definition 96.2 (Pseudo-random Function). A family of functions
 { f s : {0, 1}|s| → {0, 1}|s| }s∈{0,1}∗ is pseudo-random if
      • (Easy to compute): f s ( x ) can be computed by a p.p.t. algo-
        rithm that is given input s and x
      • (Pseudorandom): {s ← {0, 1}n : f s }n ≈ { F ← RFn : F }n .

 Note that in the definition of a PRF, it is critical that the seed s
 to the PRF is not revealed; otherwise it is easy to distinguish f s
 from a random function: simply ask the oracle a random query
 x and check whether the oracle’s reply equals f s ( x ).
 3.8. Pseudorandom Functions                                                         97


    Also note that the number of pseudorandom functions is
 much smaller than the number of random function (for the same
 input lenghts); indeed all pseudorandom functions have a short
 description, whereas random functions in general do not.

.Theorem 97.3 If a pseudorandom generator exists, then pseudoran-
 dom functions exist.

 Proof. We have already shown that any pseudorandom generator
 g is sufficient to construct a pseudorandom generator g0 that has
 polynomial expansion. So, without loss of generality, let g be a
 length-doubling pseudorandom generator.

           g:           x                      g0 ( x )         g1 ( x )


                     n bits                    n bits           n bits

 Then we define f s as follows to be a pseudorandom function:

             f s (b1 b2 . . . bn ) = gbn ( gbn−1 (· · · ( gb1 (s)) · · · ))

 f keeps only one side of the pseudorandom generator at each
 of n iterations. Thus, the possible outputs of f for a given input
 form a tree; the first three levels are shown in the following
 diagram. The leaves of the tree are the output of f .

                                           s


              s 0 = g0 ( s )                              s 1 = g1 ( s )


    s00 = g0 (s0 )      s01 = g1 (s0 )         s10 = g0 (s1 )       s11 = g1 (s1 )

     The intuition about why f is a pseudorandom function is
 that a tree of height n contains 2n leaves, so exponentially many
 values can be indexed by a single function with n bits of input.
 Thus, each unique input to f takes a unique path through the
 tree. The output of f is the output of a pseudorandom generator
 on a random string, so it is also pseudo-random.
98         chapter 3. indistinguishability & pseudo-randomness


    One approach to the proof is to look at the leaves of the
tree. Build a sequence of hybrids by successively replacing each
leaf with a random distribution. This approach, however, does
not work because our hybrid lemma does not apply when there
are exponentially many hybrids. Instead, we form hybrids by
replacing successive levels of the tree: hybrid HFin is formed
by picking all levels through the ith uniformly at random, then
applying the tree construction as before.


                                                          random




     Note that HF1n = {s ← {0, 1}n : f s (·)} (picking only the seed
at random), which is the distribution defined originally. Further,
HFnn = RFn (picking the leaves at random).
     Thus, if D can distinguish F ← RFn and f s for a randomly
chosen s, then D distinguishes F1 ← HF1n and Fn ← HFnn with
probability e. By the hybrid lemma, there exists some i such that
D distinguishes HFin and HFin+1 with probability e/n.
     The difference between HFin and HFin+1 is that level i + 1 in
HFn is g(Un ), whereas in HFin+1 , level i + 1 is Un . Afterwards,
   i

both distributions continue to use g to construct the tree.
     To finish the proof, we will construct one more set of hybrid
distributions. Recall that there is some polynomial p(n) such
that the number of queries made by D is bounded by p(n). So,
we can now apply the first hybrid idea suggested above: define
              j
hybrid HHFn that picks F from HFni , and answer the first j new
queries using F, then answer the remaining queries using HFni+1 .
     But now there are only p(n) hybrids, so the hybrid lemma
                                          j           j +1
applies, and D can distinguish HHFn and HHFn for some j
                                            j          j +1
with probability e/(np(n)). But HHFn and HHFn differ only
              j +1
in that HHFn answers its j + 1st query with the output of a
pseudorandom generator on a randomly chosen value, whereas
 3.9. Construction of Multi-message Secure Encryption              99

      j
 HHFn answers its j + 1st query with a randomly chosen value.
                    j
 As queries to HHFn can be emulated in p.p.t. (we here rely on the
 equivalence between the combinatorial and the computational
 view of a random function; we omit the details), it follows by
 closure under efficient operations that D contradicts the pseudo-
 random property of g.                                          


 3.9 Construction of Multi-message Secure
     Encryption
 The idea behind our construction is to use a pseudorandom func-
 tion in order to pick a separate random pad for every message.
 In order to make decryption possible, the ciphertext contains the
 input on which the pseudo-random function is evaluated.

 algorithm 99.1: Many-message Encryption Scheme


  Assume m ∈ {0, 1}n and let { f k } be a PRF family.
  Gen(1n ) : k ← Un
  Enck (m) : Pick r ← Un . Output (r, m ⊕ f k (r ))
  Deck ((r, c)) : Output c ⊕ f k (r )




.Theorem 99.2 (Gen, Enc, Dec) is a many-message secure encryption
 scheme.

 Proof. Assume for contradiction that there exists a n.u. p.p.t.
 distinguisher D, and a polynomial p(·) such that for infinitely
 many n, there exists messages m̄ = {m0 , m1 . . . , mq(n) } and m̄0 =
 {m00 , m10 . . . , m0q(n) } such that D distinguishes between encryp-
 tions of m̄ and m̄0 w.p. p(1n) . (To simplify notation, here—and in
 subsequent proofs—we sometimes omit n from our notation and
 let mi denote min , whenever n is clear from the context). Con-
 sider the following sequence of hybrid distributions: As above, it
 should be clear that Hi denotes Hni .
100           chapter 3. indistinguishability & pseudo-randomness


      • H1 : real encryptions of m0 , m1 . . . , mq(n)

                 s ← {0, 1}n
                 r0 , . . . , rq(n) ← {0, 1}n
                 (r0 , m0 ⊕ f s (r0 )), . . . , (rq(n) , mq(n) ⊕ f s (rq(n) ))

        This is precisely what the adversary sees when receiving
        the encryptions of m0 , . . . , mq(n) .
      • H2 : Replace f with a truly random function R:
                  R ← RFn
                  r0 , . . . , rq(n) ← {0, 1}n
                  (r0 , m0 ⊕ R(r0 )), . . . , (rq(n) , mq(n) ⊕ R(rq(n) ))

      • H3 – using OTP on m0 , m1 , . . . , mq(n)

                           p0 . . . pq(n) ← {0, 1}n
                           r0 , . . . , rq(n) ← {0, 1}n
                           (r0 , m0 ⊕ p0 , . . . , m q ( n ) ⊕ p q ( n ) )

      • H4 – using OTP on m00 , m10 , . . . , m0q(n)

                             p0 . . . pq(n) ← {0, 1}n
                            r0 , . . . , rq(n) ← {0, 1}n
                            (r0 , m00 ⊕ p0 , . . . m0q(n) ⊕ pq(n)

      • H5 – Replace f with a truly random function R:
                  R ← {{0, 1}n → {0, 1}n }
                  r0 , . . . , rq(n) ← {0, 1}n
                  (r0 , m00 ⊕ R(r0 ), . . . (rq(n) , m0q(n) ⊕ R(rq(n) ))}

      • H6 – real encryptions of m00 , m10 , . . . , m0q(n)

                  s ← {0, 1}n
                  r0 , . . . , rq(n) ← {0, 1}n
                  (r0 , m00 ⊕ f s (r0 ), . . . , (rq(n) , m0q(n) ⊕ f s (rq(n) )}
3.10. Public Key Encryption                                       101


By the Hybrid Lemma, D distinguishes between to adjacent
hybrid distributions with inverse polynomial probability (for
infinitely many n). We show that this is a contradiction:

   • First, note that D distinguish between H1 and H2 only with
     negligible probability; otherwise (by closure under efficient
     operations) we contradict the pseudorandomness property
     of { f s }n .
     The same argument applies for H6 and H5 .

   • H2 and H3 are “almost” identical except for the case when
     ∃i, j such that ri = r j , but this happens only with probability

                                  q(n)
                                      
                                         · 2− n ,
                                   2

     which is negligible; thus, D can distinguishes between
     H2 and H3 only with negligible probability. The same
     argument applies for H4 and H5 .

   • Finally, H3 and H4 are identical by the perfect secrecy of
     the OTP.

This contradicts that D distinguishes two adjacent hybrids.        


3.10 Public Key Encryption
So far, our model of communication allows the encryptor and
decryptor to meet in advance and agree on a secret key which
they later can use to send private messages. Ideally, we would
like to drop this requirement of meeting in advance to agree on a
secret key. At first, this seems impossible. Certainly the decryp-
tor of a message needs to use a secret key; otherwise, nothing
prevents the eavesdropper from running the same procedure
as the decryptor to recover the message. It also seems like the
encryptor needs to use a key because otherwise the key cannot
help to decrypt the cyphertext.
    The flaw in this argument is that the encrypter and the de-
cryptor need not share the same key, and in fact this is how
public key cryptography works. We split the key into a secret
 102        chapter 3. indistinguishability & pseudo-randomness


 decryption key sk and a public encryption key pk. The public
 key is published in a secure repository, where anyone can use it
 to encrypt messages. The private key is kept by the recipient so
 that only she can decrypt messages sent to her.
     We define a public key encryption scheme as follows:

.Definition 102.1 (Public Key Encryption Scheme). A triple of
 algorithms (Gen, Enc, Dec) is a public key encryption scheme if

   1. ( pk, sk) ← Gen(1n ) is a p.p.t. algorithm that produces a key
      pair ( pk, sk)
   2. c ← Enc pk (m) is a p.p.t. algorithm that given pk and m ∈
      {0, 1}n produces a ciphertext c.
   3. m ← Decsk (c) is a deterministic algorithm that given a
      ciphertext c and secret key sk produces a message m ∈
      {0, 1}n ∪ ⊥.
   4. There exists a polynomial-time algorithm M that on input
      (1n , i ) outputs the ith n-bit message (if such a message exists)
      according to some order.
   5. For all n ∈ N, m ∈ {0, 1}n

           Pr ( pk, sk) ← Gen(1n ) : Decsk (Enc pk (m)) = m = 1
                                                          


     We allow the decryption algorithm to produce a special sym-
 bol ⊥ when the input ciphertext is “undecipherable.” The secu-
 rity property for public-key encryption can be defined using an
 experiment similar to the ones used in the definition for secure
 private key encryption.

.Definition 102.2 (Secure Public Key Encryption). The public key
 encryption scheme (Gen, Enc, Dec) is said to be secure if for all
 non uniform p.p.t. D, there exists a negligible function e(·) such
 that for all n ∈ N, m0 , m1 ∈ {0, 1}n , D distinguishes between the
 the following distributions with probability at most e(n):

    • {( pk, sk) ← Gen(1n ) : ( pk, Enc pk (m0 ))}n
    • {( pk, sk) ← Gen(1n ) : ( pk, Enc pk (m1 ))}n
3.10. Public Key Encryption                                                 103


   With this definitions, there are some immediate impossibility
results:

Perfect secrecy Perfect secrecy is not possible (even for small
     message spaces) since an unbounded adversary could sim-
     ply encrypt every message in {0, 1}n with every random
     string and compare with the challenge ciphertext to learn
     the underlying message.

Deterministic encryption It is also impossible to have a deter-
     ministic encryption algorithm because otherwise an adver-
     sary could simply encrypt and compare the encryption
     of m0 with the challenge ciphertext to distinguish the two
     experiments.

    As with the case of private-key encryption, we can extend the
definition to multi-message security. Fortunately, for the case of
public-key encryption, multi-message security is equivalent to
single-messages security. This follows by a simple application of
the hybrid lemma, and closure under efficient operations; the key
point here is that we can efficiently generate encryptions of any
message, without knowing the secret key (this was not possible,
in the case of private-key encryption). We leave it as an exercise
to the reader to complete the proof.
    We can consider a weaker notion of “single-bit” secure en-
cryption in which we only require that encryptions of 0 and 1
are indistinguishable. Any single-bit secure encryption can be
turned into a secure encryption scheme by simply encrypting
each bit of the message using the single-bit secure encryption;
the security of the new scheme follows directly from the multi-
message security (which is equivalent to traditional security) of
the single-bit secure encryption scheme.2

3.10.1 Constructing a Public Key Encryption Scheme
Trapdoor permutations seem to fit the requirements for a public
key cryptosystem. We could let the public key be the index i of
    2 As we discuss in a later chapter, this same argument does not apply for

stronger definitions of encryption such as chosen-ciphertext security. In fact, a
more sophisticated argument is needed to show the same simple result.
 104          chapter 3. indistinguishability & pseudo-randomness


 the function to apply, and the private key be the trapdoor t. Then
 we might consider Enci (m) = f i (m), and Deci,t (c) = f i−1 (c). This
 makes it easy to encrypt, and easy to decrypt with the public key,
 and hard to decrypt without. Using the RSA function defined in
 Theorem 53.2, this construction yields the commonly used RSA
 cryptosystem.
        However, according to our definition, this construction does
 not yield a secure encryption scheme. In particular, it is de-
 terministic, so it is subject to comparison attacks. A better
 scheme (for single-bit messages) is to let Enci ( x ) = {r ← {0, 1}n :
 h f i (r ), b(r ) ⊕ mi} where b is a hardcore bit for f . As we show,
 the scheme is secure, as distinguishing encryptions of 0 and
 1 essentially requires predicting the hardcore bit of a one-way
 permutation.
 algorithm 104.3: 1-Bit Secure Public Key Encryption

  Gen(1n ) : ( f i , f i−1 ) ← GenT (1n ). Output ( pk, sk) ← (( f i , bi ), f i−1 )
  Enc pk (m): Pick r ← {0, 1}n . Output ( f i (r ), bi (r ) ⊕ m).
  Decsk (c1 , c2 ): Compute r ← f i−1 (c1 ). Output bi (r ) ⊕ c2 .

 Here, ( f i , f −1 )i∈ I is a family of one-way trapdoor permutations
 and bi is the hard-core bit corresponding to f i . Let GenT be the
 p.p.t. that samples a trapdoor permutation index from I.

.Theorem 104.4 If trapdoor permutations exist, then scheme 104.3 is
 a secure single-bit public-key encryption system.

 Proof: As usual, assume for contradiction that there exists a
 n.u. p.p.t. D and a polynomial p(·), such that D distinguishes
 {( pk, sk) ← Gen(1n ) : ( pk, Enc pk (0))} and {( pk, sk) ← Gen(1n ) :
 ( pk, Enc pk (1))} w.p. p(1n) for infinitely many n. By the prediction
 lemma, there exist a machine A such that
    Pr m ← {0, 1}; ( pk, sk) ← Gen(1n ) : D ( pk, Enc pk (m)) = m
                                                                   

           1   1
       >     +
           2 2p(n)
 We can now use A to construct a machine A0 that predicts the
 hard-core predicate b(·):
 3.11. El-Gamal Public Key Encryption scheme                             105


    • A0 on input ( pk, y) picks c ← {0, 1}, m ← A( pk, (y, c)), and
      outputs c ⊕ m.
 Note that,

 Pr ( pk, sk) ← Gen(1n ); r ← {0, 1}n : A0 ( pk, f pk (r )) = b(r )
                                                                    

             ( pk, sk) ← Gen(1n );
                                                                        

   = Pr  r ← {0, 1}n ;             : A( pk, ( f pk (r ), c)) ⊕ c = b(r )
             c ← {0, 1}
             ( pk, sk) ← Gen(1n );
                                                                          

   = Pr  r ← {0, 1}n ;             : A( pk, ( f pk (r ), m ⊕ b(r ))) = m
             m ← {0, 1}
                                                                
            m ← {0, 1}
   = Pr                            : A( pk, Enc pk (m)) = m
            ( pk, sk) ← Gen(1n )
      1        1
   ≥ +              .
      2 2p(n)
                                                                          

 3.11 El-Gamal Public Key Encryption scheme
 The El-Gamal public key encryption scheme is a popular and
 simple public key encryption scheme that is far more efficient
 than the one just presented. However, this efficiency requires
 us to make a new complexity assumption called the Decisional
 Diffie-Hellman Assumption (DDH).

.Assumption 105.1 (Decisional Diffie-Hellman (DDH)) The fol-
 lowing ensembles are computationally indistinguishable
      n                                                        o
        p ← Π̃n , y ← Genq , a, b ← Zq : p, y, y a , yb , y ab     ≈
                                                                 n
           n                                                         o
             p ← Π̃n , y ← Genq , a, b, z ← Zq : p, y, y a , yb , yz
                                                                     n

 Here the term Π̃n refers to the special subset of safe primes

            Π̃n = { p | p ∈ Πn and p = 2q + 1, q ∈ Πn−1 }

 The corresponding q is called a Sophie Germain prime. We use such
 a multiplicative group G = Z p because it has a special structure
106        chapter 3. indistinguishability & pseudo-randomness


that is convenient to work with. First, G has a subgroup Gq of
order q, and since q is prime, Gq will be a cyclic group. Thus, it is
easy to pick a generator of the group Gq (since every element is
a generator). When p = 2q + 1, then the subgroup Gq consists of
all of the squares modulo p. Thus, choosing a generator involves
simply picking a random element a ∈ G and computing a2 . Note
that all of the math is still done in the “big” group, and therefore
modulo p.
    It is crucial for the DDH assumption that the group within
which we work is a prime-order group. In a prime order group, all
elements except the identity have the same order. On the other
hand, in groups like G, there are elements of order 2, q and 2q,
and it is easy to distinguish between these cases. For example, if
one is given a tuple T = ( p, y, g, h, f ) and one notices that both
g, h are of order q but f is of order 2q, then one can immediately
determine that tuple T is not a DDH-tuple.
    Notice that the DDH assumption implies the discrete-log
assumption (Assumption 52.2) since after solving the discrete
log twice on the first two components, it is easy to distinguish
whether the third component is y ab or not.
    We now construct a Public Key Encryption scheme based on
the DDH assumption.
algorithm 106.2: El-Gamal Secure Public Key Encryption

 Gen(1n ): Pick a safe prime p = 2q + 1 of length n. Choose
     a random element g ∈ Z p and compute h ← g2 mod p.
     Choose a ← Zq . Output pk ← ( p, h, h a mod p) and sk as
     sk ← ( p, h, a).

 Enc pk (m): Choose b ← Zq . Output (hb , h ab · m mod p).

 Decsk (c = (c1 , c2 )): Output c2 /c1a mod p.


    Roughly speaking, this scheme is secure assuming the DDH
assumption since h ab is indistinguishable from a random element
and hence, by closure under efficient operations, h ab · m is indis-
tinguishable from a random element too. We leave the formal
proof as an exercise to the reader.
 3.12. A Note on Complexity Assumptions                        107


.Theorem 107.3 If the DDH Assumption holds, then scheme 106.2 is
 secure.


 3.12 A Note on Complexity Assumptions
 During these first two chapters, we have studied a hierarchy
 of constructions. At the bottom of this hierarchy are computa-
 tionally difficult problems such as one-way functions, one-way
 permutations, and trapdoor permutations. Our efficient con-
 structions of these objects were further based on specific number-
 theoretic assumptions, including factoring, RSA, discrete log, and
 decisional Diffie-Hellman.
     Using these hard problems, we constructed several primi-
 tives: pseudorandom generators, pseudorandom functions, and
 private-key encryption schemes. Although our constructions
 were usually based on one-way permutations, it is possible to
 construct these same primitives using one-way functions. Further,
 one-way functions are a minimal assumption, because the exis-
 tence of any of these primitives implies the existence of one-way
 functions.
     Public-key encryption schemes are noticeably absent from
 the list of primitives above. Although we did construct two
 public key encryption schemes, it is unknown how to base such
 a construction on one-way functions. Moreover, it is known to
 be impossible to create a black-box construction from one-way
 functions.
```
