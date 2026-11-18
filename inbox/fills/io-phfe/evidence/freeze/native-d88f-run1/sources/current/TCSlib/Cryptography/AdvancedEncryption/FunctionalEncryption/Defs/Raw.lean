/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.MatrixDH.Parameters
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Function classes and public-key functional encryption

The public and private inputs and function descriptions have fixed-width wire representations.
The class parameter and evaluation codomain are arbitrary. A group-based public-parameter
generator fixes the class parameter; it does not restrict which function classes can be used.

## Main definitions

* `FnClass`: a parameterized function class with public and private inputs.

## Main results

The syntax separates deterministic cores and finite exact draws from efficiency obligations.

## References

* [GJLS21] R. Gay, A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Simple-to-State Hard Problems: New Assumptions, New Techniques, and Simplification*,
  EUROCRYPT 2021; full version, Cryptology ePrint Archive, Report 2020/764,
  revision of 3 January 2025, Definitions 4.1-4.3 and 4.6, and Section 9.
* [Wee20] H. Wee, *Functional Encryption for Quadratic Functions from k-Lin, Revisited*,
  TCC 2020; full version, Cryptology ePrint Archive, Report 2020/1420, Section 2.2.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing

/-- A function class has a public input, a private input, a function description, and an
evaluation map into its parameter-dependent output type [GJLS21, Section 4, p. 18].

The inputs and descriptions use fixed-width bit strings. The parameter and output type remain
arbitrary; in partially hiding encryption the parameter is the drawn group's order, and the
evaluation occurs in the exponent before the scheme embeds the value into the target group.
This separates scalar simulator leakage from the decryption codomain. -/
structure FnClass where
  /-- The width of the public input. -/
  pubLen : PolyExpr
  /-- The width of the private input. -/
  privLen : PolyExpr
  /-- The width of a function description. -/
  fnLen : PolyExpr
  /-- The class parameter at each security parameter. -/
  Prm : ℕ → Type
  /-- The evaluation codomain before the scheme's output embedding. -/
  Out : (κ : ℕ) → Prm κ → Type
  /-- A canonical wire encoding for a function value supplied to a simulator. -/
  encValue : (κ : ℕ) → (π : Prm κ) → Out κ π → List Bool
  /-- The value encoding preserves the simulator's allowed value. -/
  encValue_injective : ∀ κ π, Function.Injective (encValue κ π)
  /-- Evaluation of a function on the public and private inputs. -/
  eval : (κ : ℕ) → (π : Prm κ) → (Fin (fnLen.eval κ) → Bool) →
    (Fin (pubLen.eval κ) → Bool) → (Fin (privLen.eval κ) → Bool) → Out κ π

/-- The raw syntax of public-key functional encryption consists of deterministic cores and
finite exact draws, with deterministic decryption [GJLS21, Definition 4.1].

All key and ciphertext types depend on the public parameters so group-valued objects retain
their drawn group. Inputs and function descriptions use the function class's fixed-width
wire types. The output embedding is injective and fixed by the public parameters; it may map
scalar function values into the target group. Efficiency is added by `FEScheme`. -/
structure FEScheme.Raw (C : FnClass) where
  /-- The uniform group-description generator. -/
  G : BilinearGen
  /-- The class parameter fixed by public parameters. -/
  cprm : (κ : ℕ) → PublicParams G κ → C.Prm κ
  /-- The width of an encoded master public key. -/
  mpkLen : PolyExpr
  /-- The width of an encoded master secret key. -/
  mskLen : PolyExpr
  /-- The width of an encoded function key. -/
  skLen : PolyExpr
  /-- The width of the ciphertext excluding its separately public input. -/
  ctLen : PolyExpr
  /-- The width of a successful decryption output. -/
  decOutLen : PolyExpr
  /-- Master public keys over the drawn group. -/
  MPK : (κ : ℕ) → PublicParams G κ → Type
  /-- Master secret keys over the drawn group. -/
  MSK : (κ : ℕ) → PublicParams G κ → Type
  /-- Functional decryption keys over the drawn group. -/
  SK : (κ : ℕ) → PublicParams G κ → Type
  /-- Ciphertexts over the drawn group. -/
  CT : (κ : ℕ) → PublicParams G κ → Type
  /-- The decryption codomain, before the optional failure marker. -/
  DecOut : (κ : ℕ) → PublicParams G κ → Type
  /-- Interpret a function value in the decryption codomain. -/
  embed : (κ : ℕ) → (pp : PublicParams G κ) → C.Out κ (cprm κ pp) → DecOut κ pp
  /-- The embedding loses no information about the function value. -/
  embed_injective : ∀ κ pp, Function.Injective (embed κ pp)
  /-- The single draw type of setup. -/
  SetupDraw : (κ : ℕ) → PublicParams G κ → Type
  /-- Setup draws have a finite uniform law. -/
  [setupDrawFintype : ∀ κ pp, Fintype (SetupDraw κ pp)]
  /-- Setup draws are nonempty. -/
  [setupDrawNonempty : ∀ κ pp, Nonempty (SetupDraw κ pp)]
  /-- The deterministic setup core. -/
  setupCore : (κ : ℕ) → (pp : PublicParams G κ) → SetupDraw κ pp → MPK κ pp × MSK κ pp
  /-- The single draw type of encryption. -/
  EncDraw : (κ : ℕ) → (pp : PublicParams G κ) → MPK κ pp →
    (Fin (C.pubLen.eval κ) → Bool) → (Fin (C.privLen.eval κ) → Bool) → Type
  /-- Encryption draws have a finite uniform law. -/
  [encDrawFintype : ∀ κ pp pk x y, Fintype (EncDraw κ pp pk x y)]
  /-- Encryption draws are nonempty. -/
  [encDrawNonempty : ∀ κ pp pk x y, Nonempty (EncDraw κ pp pk x y)]
  /-- The deterministic encryption core, with both public and private inputs. -/
  encCore : (κ : ℕ) → (pp : PublicParams G κ) → (pk : MPK κ pp) →
    (x : Fin (C.pubLen.eval κ) → Bool) → (y : Fin (C.privLen.eval κ) → Bool) →
    EncDraw κ pp pk x y → CT κ pp
  /-- The single draw type of key generation. -/
  KeyDraw : (κ : ℕ) → (pp : PublicParams G κ) → MSK κ pp →
    (Fin (C.fnLen.eval κ) → Bool) → Type
  /-- Key-generation draws have a finite uniform law. -/
  [keyDrawFintype : ∀ κ pp msk f, Fintype (KeyDraw κ pp msk f)]
  /-- Key-generation draws are nonempty. -/
  [keyDrawNonempty : ∀ κ pp msk f, Nonempty (KeyDraw κ pp msk f)]
  /-- The deterministic key-generation core. -/
  keyCore : (κ : ℕ) → (pp : PublicParams G κ) → (msk : MSK κ pp) →
    (f : Fin (C.fnLen.eval κ) → Bool) → KeyDraw κ pp msk f → SK κ pp
  /-- Deterministic decryption, including the public input and an optional failure result. -/
  dec : (κ : ℕ) → (pp : PublicParams G κ) → SK κ pp →
    (Fin (C.pubLen.eval κ) → Bool) → CT κ pp → Option (DecOut κ pp)
  /-- The master public key's fixed-width encoding. -/
  encMPK : (κ : ℕ) → (pp : PublicParams G κ) → MPK κ pp → Fin (mpkLen.eval κ) → Bool
  /-- The master secret key's fixed-width encoding, used by efficiency specifications. -/
  encMSK : (κ : ℕ) → (pp : PublicParams G κ) → MSK κ pp → Fin (mskLen.eval κ) → Bool
  /-- The functional key's fixed-width encoding. -/
  encSK : (κ : ℕ) → (pp : PublicParams G κ) → SK κ pp → Fin (skLen.eval κ) → Bool
  /-- The ciphertext's fixed-width encoding. -/
  encCT : (κ : ℕ) → (pp : PublicParams G κ) → CT κ pp → Fin (ctLen.eval κ) → Bool
  /-- The successful output's fixed-width encoding. -/
  encDecOut : (κ : ℕ) → (pp : PublicParams G κ) → DecOut κ pp →
    Fin (decOutLen.eval κ) → Bool
  /-- The encoding of the complete setup draw. -/
  encSetupDraw : (κ : ℕ) → (pp : PublicParams G κ) → SetupDraw κ pp → List Bool
  /-- The encoding of the complete encryption draw. -/
  encEncDraw : (κ : ℕ) → (pp : PublicParams G κ) → (pk : MPK κ pp) →
    (x : Fin (C.pubLen.eval κ) → Bool) → (y : Fin (C.privLen.eval κ) → Bool) →
    EncDraw κ pp pk x y → List Bool
  /-- The encoding of the complete key-generation draw. -/
  encKeyDraw : (κ : ℕ) → (pp : PublicParams G κ) → (msk : MSK κ pp) →
    (f : Fin (C.fnLen.eval κ) → Bool) → KeyDraw κ pp msk f → List Bool
  /-- Public-key encodings distinguish every possible setup output at fixed parameters. -/
  encMPK_inj : ∀ κ pp (r r' : SetupDraw κ pp),
    encMPK κ pp (setupCore κ pp r).1 = encMPK κ pp (setupCore κ pp r').1 →
      (setupCore κ pp r).1 = (setupCore κ pp r').1
  /-- Function-key encodings distinguish possible keys under one master secret key. -/
  encSK_inj : ∀ κ pp (r : SetupDraw κ pp) f f'
    (t : KeyDraw κ pp (setupCore κ pp r).2 f)
    (t' : KeyDraw κ pp (setupCore κ pp r).2 f'),
    encSK κ pp (keyCore κ pp (setupCore κ pp r).2 f t) =
      encSK κ pp (keyCore κ pp (setupCore κ pp r).2 f' t') →
    keyCore κ pp (setupCore κ pp r).2 f t = keyCore κ pp (setupCore κ pp r).2 f' t'
  /-- Ciphertext encodings distinguish possible ciphertexts under one public key. -/
  encCT_inj : ∀ κ pp (r : SetupDraw κ pp) x y x' y'
    (t : EncDraw κ pp (setupCore κ pp r).1 x y)
    (t' : EncDraw κ pp (setupCore κ pp r).1 x' y'),
    encCT κ pp (encCore κ pp (setupCore κ pp r).1 x y t) =
      encCT κ pp (encCore κ pp (setupCore κ pp r).1 x' y' t') →
    encCore κ pp (setupCore κ pp r).1 x y t = encCore κ pp (setupCore κ pp r).1 x' y' t'
  /-- Successful decryption values have lossless encodings. -/
  encDecOut_injective : ∀ κ pp, Function.Injective (encDecOut κ pp)

namespace FEScheme.Raw

variable {C : FnClass} (S : FEScheme.Raw C)

/-- Setup uses the finite draw instance carried by the raw bundle. -/
instance instFintypeSetupDraw (κ : ℕ) (pp : PublicParams S.G κ) :
    Fintype (S.SetupDraw κ pp) := S.setupDrawFintype κ pp

/-- Setup uses the nonempty draw instance carried by the raw bundle. -/
instance instNonemptySetupDraw (κ : ℕ) (pp : PublicParams S.G κ) :
    Nonempty (S.SetupDraw κ pp) := S.setupDrawNonempty κ pp

/-- Encryption uses the finite draw instance carried by the raw bundle. -/
instance instFintypeEncDraw (κ : ℕ) (pp : PublicParams S.G κ) (pk : S.MPK κ pp)
    (x : Fin (C.pubLen.eval κ) → Bool) (y : Fin (C.privLen.eval κ) → Bool) :
    Fintype (S.EncDraw κ pp pk x y) := S.encDrawFintype κ pp pk x y

/-- Encryption uses the nonempty draw instance carried by the raw bundle. -/
instance instNonemptyEncDraw (κ : ℕ) (pp : PublicParams S.G κ) (pk : S.MPK κ pp)
    (x : Fin (C.pubLen.eval κ) → Bool) (y : Fin (C.privLen.eval κ) → Bool) :
    Nonempty (S.EncDraw κ pp pk x y) := S.encDrawNonempty κ pp pk x y

/-- Key generation uses the finite draw instance carried by the raw bundle. -/
instance instFintypeKeyDraw (κ : ℕ) (pp : PublicParams S.G κ) (msk : S.MSK κ pp)
    (f : Fin (C.fnLen.eval κ) → Bool) :
    Fintype (S.KeyDraw κ pp msk f) := S.keyDrawFintype κ pp msk f

/-- Key generation uses the nonempty draw instance carried by the raw bundle. -/
instance instNonemptyKeyDraw (κ : ℕ) (pp : PublicParams S.G κ) (msk : S.MSK κ pp)
    (f : Fin (C.fnLen.eval κ) → Bool) :
    Nonempty (S.KeyDraw κ pp msk f) := S.keyDrawNonempty κ pp msk f

end FEScheme.Raw

end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
